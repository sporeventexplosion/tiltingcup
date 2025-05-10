#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>

#include <sodium.h>

struct Csr {
  // mtvec: 0x305 machine rw
  uint64_t mtvec;
  // mscratch: 0x340 machine rw
  uint64_t mscratch;
};

struct Hart {
  uint64_t regfile[32];
  uint64_t pc;
  Csr csr;
};

Hart hart = {};

static uint64_t n_retired = 0;

const static size_t dbg_event_buf_cap = 4096;
const static size_t dbg_max_event_len = 8;
static size_t dbg_event_buf_size = 0;
static uint64_t *dbg_event_buf;
static crypto_generichash_state dbg_event_hash_state;

void dbg_init() {
  assert(sodium_init() >= 0);
  dbg_event_buf = new uint64_t[dbg_event_buf_cap];
  assert(dbg_event_buf);

  crypto_generichash_init(&dbg_event_hash_state, nullptr, 0,
                          crypto_generichash_BYTES);
}

void dbg_force_compress_events() {
  crypto_generichash_update(&dbg_event_hash_state,
                            (unsigned char *)dbg_event_buf,
                            dbg_event_buf_size * sizeof(uint64_t));
  dbg_event_buf_size = 0;
}

void dbg_compress_events() {
  if (dbg_event_buf_size > dbg_event_buf_cap - dbg_max_event_len) {
    dbg_force_compress_events();
  }
}

static char digit_to_hex(int n) { return n + (n < 10 ? 48 : 87); }

static void bytes_to_hex_str(const unsigned char *bytes, char *str,
                             size_t byte_len) {
  for (size_t i = 0; i < byte_len; i++) {
    str[2 * i] = digit_to_hex(bytes[i] >> 4);
    str[2 * i + 1] = digit_to_hex(bytes[i] & 0xf);
  }
  str[2 * byte_len] = '\0';
}

void dbg_print_events_hash(FILE *outfile) {
  dbg_force_compress_events();
  crypto_generichash_state tmp_hash_state;
  memcpy(&tmp_hash_state, &dbg_event_hash_state,
         sizeof(crypto_generichash_state));

  unsigned char hash[8];
  crypto_generichash_final(&tmp_hash_state, hash, sizeof hash);

  char hash_hex[2 * sizeof hash + 1];
  bytes_to_hex_str(hash, hash_hex, sizeof hash);
  fprintf(outfile, "Events hash: %s\n", hash_hex);
}

void dbg_print_regfile_hash(FILE *outfile, Hart *hart) {
  unsigned char hash[8];
  crypto_generichash(hash, sizeof hash, (unsigned char *)&hart->regfile,
                     sizeof hart->regfile, nullptr, 0);

  char hash_hex[2 * sizeof hash + 1];
  bytes_to_hex_str(hash, hash_hex, sizeof hash);
  fprintf(outfile, "Register file hash: %s\n", hash_hex);
}

// initial dummy value, instruction addresses are always even
static uint64_t dbg_last_jump_src = 1, dbg_last_jump_dst = 1;
static uint64_t dbg_last_jump_count = 0;

enum {
  DBG_EVENT_BRANCH_COALESCED,
  DBG_EVENT_LOAD,
  DBG_EVENT_STORE,
  DBG_EVENT_ATOMIC,
};

void dbg_log_branch(uint64_t from, uint64_t to) {
  if (from == dbg_last_jump_src && to == dbg_last_jump_dst) {
    dbg_last_jump_count++;
    putchar('.');
  } else {
    bool first = dbg_last_jump_src & 1;
    if (!first) {
      dbg_compress_events();
      dbg_event_buf[dbg_event_buf_size++] = DBG_EVENT_BRANCH_COALESCED;
      dbg_event_buf[dbg_event_buf_size++] = dbg_last_jump_src;
      dbg_event_buf[dbg_event_buf_size++] = dbg_last_jump_dst;
      dbg_event_buf[dbg_event_buf_size++] = dbg_last_jump_count;
      putchar('\n');
    }

    dbg_last_jump_src = from;
    dbg_last_jump_dst = to;
    dbg_last_jump_count = 1;
    printf("jump from = %lx to %lx", from, to);
  }
}

void dbg_log_memory(int event, uint64_t addr, uint64_t attrs, uint64_t data) {
  dbg_compress_events();
  dbg_event_buf[dbg_event_buf_size++] = event;
  dbg_event_buf[dbg_event_buf_size++] = addr;
  dbg_event_buf[dbg_event_buf_size++] = attrs;
  dbg_event_buf[dbg_event_buf_size++] = data;
}

const char *reg_names[32] = {
    "zero  (x0)", "ra  (x1)", "sp  (x2)",  "gp  (x3)",  "tp  (x4)", "t0  (x5)",
    "t1  (x6)",   "t2  (x7)", "s0  (x8)",  "s1  (x9)",  "a0 (x10)", "a1 (x11)",
    "a2 (x12)",   "a3 (x13)", "a4 (x14)",  "a5 (x15)",  "a6 (x16)", "a7 (x17)",
    "s2 (x18)",   "s3 (x19)", "s4 (x20)",  "s5 (x21)",  "s6 (x22)", "s7 (x23)",
    "s8 (x24)",   "s9 (x25)", "s10 (x26)", "s11 (x27)", "t3 (x28)", "t4 (x29)",
    "t5 (x30)",   "t6 (x31)",
};

const uint32_t reset_vec[10] = {
    0x00000297,
    0x02828613,
    0xf1402573,

    0x0202b583,
    0x0182b283,

    0x00028067,
    // start addr
    0x80000000,
    0,
    // fdt addr
    0xbfe00000,
    0,
};

struct MemoryMapEntry {
  uint64_t start, size;
  void *ptr;
};

std::vector<MemoryMapEntry> memory_map;
char *dram;

static void build_memory_map(uint64_t dram_size) {
  assert(memory_map.empty());
  dram = new char[dram_size];
  assert(dram);
  // NOTE: keep the start addresses aligned to at least 4 KB (sizes don't have
  // to be round)
  memory_map = {
      MemoryMapEntry{0x1000, 0x1000, (void *)reset_vec},
      MemoryMapEntry{0x80000000, dram_size, (void *)dram},
  };
}

static void load_elf_to_physical_memory(const char *filepath) {
  int fd = open(filepath, O_RDONLY);
  assert(fd >= 0);

  struct stat st;
  assert(fstat(fd, &st) != -1);
  size_t filelen = st.st_size;
  assert(filelen > 0);

  char *data = (char *)mmap(nullptr, filelen, PROT_READ, MAP_PRIVATE, fd, 0);
  assert(data != MAP_FAILED);

  close(fd);

  assert(filelen >= 64);

  uint64_t magic = *(uint64_t *)data;
  assert(magic == 0x00010102464c457ful); // little-endian 64-bit system v
  uint16_t e_type = *(uint16_t *)(data + 0x10);
  assert(e_type == 2); // executable
  uint16_t e_machine = *(uint16_t *)(data + 0x12);
  assert(e_machine == 243); // risc-v

  uint64_t e_phoff = *(uint64_t *)(data + 0x20);
  uint16_t e_phnum = *(uint16_t *)(data + 0x38);
  size_t ph_size = 0x38 * e_phnum;
  size_t ph_end = e_phoff + ph_size;
  assert(e_phoff % 8 == 0);
  assert(ph_end >= e_phoff);
  assert(ph_end < filelen);

  char *ph_end_p = data + ph_end;
  for (char *phent_p = data + e_phoff; phent_p != ph_end_p; phent_p += 0x38) {
    uint32_t p_type = *(uint32_t *)phent_p;
    if (p_type != 1 /* LOAD */)
      continue;

    uint64_t p_offset = *(uint64_t *)(phent_p + 0x8);
    uint64_t p_paddr = *(uint64_t *)(phent_p + 0x18);
    uint64_t p_filesz = *(uint64_t *)(phent_p + 0x20);
    uint64_t p_memsz = *(uint64_t *)(phent_p + 0x28);
    assert(p_filesz <= p_memsz);
    if (p_filesz == 0)
      continue;
    uint64_t file_seg_end = p_offset + p_filesz;
    assert(file_seg_end > p_offset && file_seg_end <= filelen);
    uint64_t paddr_end = p_paddr + p_filesz;
    assert(paddr_end > p_paddr);

    bool loaded = false;
    for (auto &entry : memory_map) {
      if (entry.start <= p_paddr && entry.start + entry.size > p_paddr) {
        // don't cross memory map entries
        assert(entry.start + entry.size >= paddr_end);

        char *dst = (char *)entry.ptr + (p_paddr - entry.start);
        memcpy(dst, data + p_offset, p_filesz);
        loaded = true;

        break;
      }
    }
    assert(loaded);
  }
}

static uint16_t mem_read_2b_aligned(uint64_t addr) {
  assert(addr % 2 == 0);

  for (auto &entry : memory_map) {
    if (entry.start <= addr && entry.start + entry.size > addr + 1) {
      uint64_t offset = (addr - entry.start) / 2;
      return ((uint16_t *)entry.ptr)[offset];
    }
  }
  assert(false);
}

static uint32_t mem_read_4b_aligned(uint64_t addr) {
  assert(addr % 4 == 0);

  for (auto &entry : memory_map) {
    if (entry.start <= addr && entry.start + entry.size > addr + 3) {
      uint64_t offset = (addr - entry.start) / 4;
      return ((uint32_t *)entry.ptr)[offset];
    }
  }
  assert(false);
}

static uint8_t mem_read_1b(uint64_t addr) {
  for (auto &entry : memory_map) {
    if (entry.start <= addr && entry.start + entry.size > addr) {
      uint64_t offset = addr - entry.start;
      return ((uint8_t *)entry.ptr)[offset];
    }
  }
  assert(false);
}

static uint64_t mem_read_8b_aligned(uint64_t addr) {
  assert(addr % 8 == 0);

  for (auto &entry : memory_map) {
    if (entry.start <= addr && entry.start + entry.size > addr + 7) {
      uint64_t offset = (addr - entry.start) / 8;
      return ((uint64_t *)entry.ptr)[offset];
    }
  }
  assert(false);
}

static void mem_write_4b_aligned(uint64_t addr, uint32_t data) {
  assert(addr % 4 == 0);

  for (auto &entry : memory_map) {
    if (entry.start <= addr && entry.start + entry.size > addr + 3) {
      uint64_t offset = (addr - entry.start) / 4;
      ((uint32_t *)entry.ptr)[offset] = data;
      return;
    }
  }
  assert(false);
}

static void mem_write_8b_aligned(uint64_t addr, uint64_t data) {
  assert(addr % 8 == 0);

  for (auto &entry : memory_map) {
    if (entry.start <= addr && entry.start + entry.size > addr + 7) {
      uint64_t offset = (addr - entry.start) / 8;
      ((uint32_t *)entry.ptr)[offset] = data;
      return;
    }
  }
  assert(false);
}

static uint32_t fetch_insn(uint64_t addr) {
  assert(addr % 2 == 0);
  for (auto &entry : memory_map) {
    if (entry.start <= addr) {
      if (entry.start + entry.size > addr + 3) {
        // unconditionally fetch 4 bytes
        uint64_t offset = (addr - entry.start);
        uint32_t ret;
        memcpy(&ret, (char *)entry.ptr + offset, 4);
        return ret;
      } else if (entry.start + entry.size > addr + 1) {
        // very unlikely: instruction straddles 2 memory map entries, fetch in 2
        // parts if not compressed
        //
        // can't straddle more than 2 entries because each entry is
        // required to start on a 4K boundary
        uint32_t insn = mem_read_2b_aligned(addr);
        if ((insn & 3) == 3) {
          insn |= (uint32_t)mem_read_2b_aligned(addr + 2) << 16;
        }
        return insn;
      }
    }
  }
  assert(false);
}

uint64_t get_csr_next_value(uint64_t old, uint64_t next, uint8_t op_type) {
  switch (op_type) {
  case 0b01:
    // csrrw
    return next;
  case 0b10:
    // csrrs
    return old | next;
  case 0b11:
    // csrrc:
    return old & ~next;
  default:
    assert(false);
  }
}

void step() {
  bool todo = false;

  // fetch
  uint32_t op = fetch_insn(hart.pc);

  // decode
  bool compressed = (op & 3) != 3;

  uint8_t opc = 0;
  uint8_t funct3 = 0;
  uint8_t funct7 = 0;
  uint8_t rd = 0;
  uint8_t rs1 = 0;
  uint8_t rs2 = 0;

  uint64_t cimm64 = 0;
  if (compressed) {
    // expand compressed instructions
    uint8_t cmap = op & 3;
    uint8_t cfunct3 = (op >> 13) & 0x7;
    bool cbit12 = op & 0x1000;
    uint8_t crds1 = (op >> 7) & 0x1f;
    uint8_t crs2 = (op >> 2) & 0x1f;
    uint8_t crds1p = (crds1 & 0x7) | 0x8;
    uint8_t crds2p = (crs2 & 0x7) | 0x8;

    uint64_t cimm6_sext64 = -((int64_t)(op & 0x1000) >> 7) | ((op & 0x7c) >> 2);
    cimm64 = cimm6_sext64;

    if (cmap == 0b00) {
      // Map 0b00

      uint64_t cimm5_lsd_zext64 = ((op & 0x1c00) >> 7) | ((op & 0x60) << 1);

      switch (cfunct3) {
      case 0b000:
        // c.addi4spn, expands to addi rd', x2, imm
        //  12 |  11 |  10 |   9 |   8 |   7 |   6 |   5
        //   5 |   4 |   9 |   8 |   7 |   6 |   2 |   3
        opc = 0b00100;
        funct3 = 0b000;
        rd = crds2p;
        rs1 = 2;
        cimm64 = ((op & 0x1800) >> 7) | ((op & 0x780) >> 1) |
                 ((op & 0x40) >> 4) | ((op & 0x20) >> 2);

        if (cimm64 == 0) {
          // all-zeros instruction
          todo = true;
        }
        fprintf(stderr, "cimm8_addi4spn = %lu, rd = %d, rs = %d\n", cimm64, rd,
                rs1);
        break;

      case 0b111:
        // c.sd, expands to sd rs2′, offset(rs1′)
        // TODO: verify this works
        todo = true;

        opc = 0b01000;
        funct3 = 0b011;
        rs1 = crds1p;
        rs2 = crds2p;
        cimm64 = cimm5_lsd_zext64;
        fprintf(stderr, "cimm5_lsd_zext64 = %lu, rs1 = %d, rs2 = %d\n",
                cimm5_lsd_zext64, rs1, rs2);
        break;
      default:
        todo = true;
      }
    } else if (cmap == 0b01) {
      // Map 0b01

      switch (cfunct3) {
      case 0b000:
        // c.addi, expands to addi rd, rd, imm
        opc = 0b00100;
        funct3 = 0b000;
        rd = crds1;
        rs1 = crds1;
        break;
      case 0b010:
        // c.li, expands to addi rd, x0, imm
        opc = 0b00100;
        funct3 = 0b000;
        rd = crds1;
        rs1 = 0;
        break;
      case 0b011:
        if (cimm6_sext64 != 0) {
          rd = crds1;
          rs1 = crds1;
          if (crds1 == 2) {
            // c.addi16sp, expands to addi x2, x2, imm
            //  12 |  11 |  10 |   9 |   8 |   7 |   6 |   5 |   4 |   3 |   2
            //   9 |                             |   4 |   6 |   8 |   7 |   5

            opc = 0b00100;
            funct3 = 0b000;
            cimm64 = -((int64_t)(op & 0x1000) >> 3) | ((op & 0x40) >> 2) |
                     ((op & 0x20) << 1) | ((op & 0x18) << 4) |
                     ((op & 0x4) << 3);

          } else {
            // c.lui, expands to lui rd, imm
            opc = 0b01101;
            cimm64 = cimm6_sext64 << 12;
          }
        } else {
          // reserved
          todo = true;
        }
        break;
      case 0b101:
        // c.j, expands to jal x0, offset
        //  12 |  11 |  10 |   9 |   8 |   7 |   6 |   5 |   4 |   3 |   2
        //  11 |   4 |   9 |   8 |  10 |   6 |   7 |   3 |   2 |   1 |   5

        // always a multiple of two
        opc = 0b11011;
        rd = 0;
        cimm64 = -((int64_t)(op & 0x1000) >> 1) | ((op & 0x800) >> 7) |
                 ((op & 0x600) >> 1) | ((op & 0x100) << 2) |
                 ((op & 0x80) >> 1) | ((op & 0x40) << 1) | ((op & 0x38) >> 2) |
                 ((op & 0x4) << 3);
        break;
      default:
        todo = true;
      }
    } else if (cmap == 0b10) {
      // Map 0b10

      uint64_t cimm6_lsdsp_zext64 = ((op & 0x1c00) >> 7) | ((op & 0x380) >> 1);

      switch (cfunct3) {
      case 0b100:
        if (cbit12) {
          if (crs2 == 0) {
            // TODO: jalr, ebreak
            todo = true;
          } else {
            // c.add, expands to add rd, rd, rs2
            opc = 0b01100;
            funct3 = 0b000;
            funct7 = 0b0000000;
            rd = crds1;
            rs1 = crds1;
            rs2 = crs2;
          }
        } else {
          if (crs2 == 0) {
            if (crds1 == 0) {
              // TODO: this is reserved
              todo = true;
            } else {
              // c.jr, expands to jalr x0, 0(rs1)
              //
              // we can leave the immediate along here because decoding this
              // instruction with the 6-bit immediate format results in a
              // decoded immediate of 0
              opc = 0b11001;
              funct3 = 0b000;
              rd = 0;
              rs1 = crds1;
            }
          } else {
            // c.mv, officially expands to add rd, x0, rs2,
            // but we instead expand to addi rd, rs2, 0 without changing the
            // semantics (see the instruction set manual)
            opc = 0b00100;
            funct3 = 0b000;
            rd = crds1;
            rs1 = crs2;
            cimm64 = 0;
          }
        }
        break;
      case 0b111:
        // c.sdsp, expands to sd rs2, offset(x2)
        opc = 0b01000;
        funct3 = 0b011;
        rs1 = 2;
        rs2 = crs2;
        cimm64 = cimm6_lsdsp_zext64;
        break;
      default:
        todo = true;
      }
    }
  } else {
    opc = (op >> 2) & 0x1f;
    funct3 = (op >> 12) & 0x7;
    funct7 = op >> 25;
    rd = (op >> 7) & 0x1f;
    rs1 = (op >> 15) & 0x1f;
    rs2 = (op >> 20) & 0x1f;

    // always a multiple of two
  }

  uint64_t imm20_u_sext64 = compressed ? cimm64 : (int32_t)(op & -0x1000);
  uint16_t imm12_i_raw = op >> 20;
  uint64_t imm12_i_sext64 = compressed ? cimm64 : (int32_t)op >> 20;
  uint64_t imm12_s_sext64 =
      compressed ? cimm64
                 : (int32_t)(((int32_t)(op & 0xfe000000u) >> 20) |
                             ((op & 0xf80) >> 7));

  uint64_t imm12_b_sext64 = (int32_t)(((int32_t)(op & 0x80000000u) >> 19) |
                                      ((op & 0x7e000000u) >> 20) |
                                      ((op & 0xf00) >> 7) | ((op & 0x80) << 4));
  // always a multiple of two
  uint64_t imm20_j_sext64 =
      compressed ? cimm64
                 : (int32_t)(((int32_t)(op & 0x80000000u) >> 11) |
                             ((op & 0x7fe00000u) >> 20) |
                             ((op & 0x100000) >> 9) | (op & 0xff000));

  // execute
  uint64_t pc = hart.pc;
  uint64_t next_pc = pc + (compressed ? 2 : 4);
  uint64_t src1 = hart.regfile[rs1];
  uint64_t src2 = hart.regfile[rs2];
  uint64_t result;

  bool do_load = false;
  bool do_store = false;
  uint64_t addr;

  bool do_jump = false;
  uint64_t jump_pc;

  bool amo = false;

  switch (opc) {
  case 0b00000:
    // integer register loads
    do_load = true;
    if (funct3 == 0b111) {
      // invalid instruction
      todo = true;
    }
    addr = src1 + imm12_i_sext64;
    break;

  case 0b00011:
    // TODO: some day this might not be a noop
    if (funct3 == 0b000) {
      // fence
      rd = 0;
    } else if (funct3 == 0b001) {
      // fence.i
      rd = 0;
    } else {
      todo = true;
    }
    break;

  case 0b00100:
    switch (funct3) {
    case 0b000:
      // addi
      result = src1 + imm12_i_sext64;
      break;
    case 0b010:
      // slti
      result = (int64_t)src1 < (int64_t)imm12_i_sext64 ? 1 : 0;
      break;
    case 0b011:
      // sltiu
      result = src1 < imm12_i_sext64 ? 1 : 0;
      break;
    case 0b100:
      // xori
      result = src1 ^ imm12_i_sext64;
      break;
    case 0b110:
      // ori
      result = src1 | imm12_i_sext64;
      break;
    case 0b111:
      // andi
      result = src1 & imm12_i_sext64;
      break;
    default:
      todo = true;
    }
    break;

  case 0b00101:
    // auipc
    result = pc + imm20_u_sext64;
    break;

  case 0b01000:
    // stores
    do_store = true;
    switch (funct3) {
    case 0b011:
      // sd
      addr = src1 + imm12_s_sext64;
      break;
    default:
      todo = true;
    }
    break;

  case 0b01011:
    // atomic ops
    if (funct3 == 0b010) {
      amo = true;
    } else {
      todo = true;
    }
    break;

  case 0b01100: {
    if (funct7 & 0b1011111) {
      todo = true;
      break;
    }

    bool is_alt_func = funct7 == 0b0100000;
    switch (funct3) {
    case 0b000:
      // add
      // sub
      result = is_alt_func ? src1 - src2 : src1 + src2;
      break;
    case 0b010:
      if (is_alt_func)
        todo = true;
      // slt
      result = (int64_t)src1 < (int64_t)src2 ? 1 : 0;
      break;
    case 0b011:
      if (is_alt_func)
        todo = true;
      // sltu
      result = src1 < src2 ? 1 : 0;
      break;
    case 0b100:
      if (is_alt_func)
        todo = true;
      // xor
      result = src1 ^ src2;
      break;
    case 0b110:
      if (is_alt_func)
        todo = true;
      // or
      result = src1 | src2;
      break;
    case 0b111:
      if (is_alt_func)
        todo = true;
      // and
      result = src1 & src2;
      break;
    default:
      todo = true;
    }
    break;
  }

  case 0b01101:
    // lui
    result = imm20_u_sext64;
    break;

  case 0b11000:
    // branch instructions
    rd = 0;
    jump_pc = pc + imm12_b_sext64;
    switch (funct3) {
    case 0b000:
      // beq
      do_jump = src1 == src2;
      break;
    case 0b001:
      // bne
      do_jump = src1 != src2;
      break;
    case 0b100:
      // blt
      do_jump = (int64_t)src1 < (int64_t)src2;
      break;
    case 0b101:
      // bge
      do_jump = (int64_t)src1 >= (int64_t)src2;
      break;
    case 0b110:
      // bltu
      do_jump = src1 < src2;
      break;
    case 0b111:
      // bgeu
      do_jump = src1 >= src2;
      break;
    default:
      todo = true;
    }
    break;

  case 0b11001:
    if (funct3 == 0b000) {
      // jalr
      do_jump = true;
      jump_pc = (src1 + imm12_i_sext64) & -0x2;
      result = next_pc;
    } else {
      todo = true;
    }
    break;

  case 0b11011:
    // jal
    do_jump = true;
    jump_pc = pc + imm20_j_sext64;
    result = next_pc;
    break;

  case 0b11100:
    if ((funct3 & 0b11) == 0) {
      // TODO: ecall, etc.
      todo = true;
    } else {
      // CSR manipulation instructions
      uint8_t op_type = funct3 & 0b11;
      bool has_imm = funct3 & 0b100;
      uint64_t src_val = has_imm ? rs1 : src1;

      // for now, we unconditionally do reads since no csr read has side effects
      bool do_csr_write = !((op_type & 0b10) && rs1 == 0);

      bool writeable = (imm12_i_raw >> 10) != 0b11;
      if (!writeable && do_csr_write) {
        todo = true;
      } else {
        switch (imm12_i_raw) {
        case 0x305:
          // mtvec: machine rw
          result = hart.csr.mtvec;
          if (do_csr_write) {
            uint64_t next = get_csr_next_value(result, src_val, op_type);
            if (next & 2) {
              // reserved
              todo = true;
            } else {
              hart.csr.mtvec = next;
            }
          }
          break;
        case 0x340:
          // mscratch: machine rw
          result = hart.csr.mscratch;
          if (do_csr_write) {
            hart.csr.mscratch = get_csr_next_value(result, src_val, op_type);
          }
          break;
        case 0xf14:
          // mhartid: machine ro
          result = 0;
          break;
        default:
          todo = true;
        }
      }
    }
    break;
  default:
    todo = true;
  }

  if (todo) {
    putchar('\n');
    fflush(stdout);

    char op_hex[9];
    if (compressed) {
      sprintf(op_hex, "%04x", (uint16_t)op);
    } else {
      sprintf(op_hex, "%08x", op);
    }
    fprintf(stderr, "TODO: pc = %lx, op = %s, n_retired = %lu\n", pc, op_hex,
            n_retired);
    fprintf(stderr, "Register state:\n");
    for (int i = 0; i < 32; i++) {
      uint64_t reg = hart.regfile[i];
      fprintf(stderr, "    %10s  0x%016lx  %ld\n", reg_names[i], reg, reg);
    }
    dbg_print_events_hash(stderr);
    dbg_print_regfile_hash(stderr, &hart);
  }
  assert(!todo);

  // memory
  if (do_load) {
    // TODO: different sizes
    bool do_zext = funct3 & 4;
    switch (funct3 & 0b11) {
    case 0b00: {
      // lb, lbu
      uint8_t result_8b = mem_read_1b(addr);
      result = do_zext ? result_8b : (int8_t)result_8b;
      dbg_log_memory(DBG_EVENT_LOAD, addr, 1 | ((uint64_t)do_zext << 12),
                     result);
      break;
    }
    case 0b01: {
      // lh, lhu
      uint16_t result_16b = mem_read_2b_aligned(addr);
      result = do_zext ? result_16b : (int16_t)result_16b;
      dbg_log_memory(DBG_EVENT_LOAD, addr, 2 | ((uint64_t)do_zext << 12),
                     result);
      break;
    }
    case 0b10: {
      // lw, lwu
      uint32_t result_32b = mem_read_4b_aligned(addr);
      result = do_zext ? result_32b : (int32_t)result_32b;
      dbg_log_memory(DBG_EVENT_LOAD, addr, 4 | ((uint64_t)do_zext << 12),
                     result);
      break;
    }
    case 0b11:
      // ld
      result = mem_read_8b_aligned(addr);
      dbg_log_memory(DBG_EVENT_LOAD, addr, 8, result);
    }
  } else if (do_store) {
    // TODO: different sizes
    mem_write_8b_aligned(addr, src2);
    dbg_log_memory(DBG_EVENT_STORE, addr, 8, src2);
  } else if (amo) {
    // do the alu operation here
    // TODO: actually look at the acquire and release fields
    // TODO: handle sizes other than 32 bits
    assert(funct3 == 0b010);

    if ((funct7 & 0xc) == 0) {
      if (src1 % 4 == 0) {
        uint32_t result_32bit = mem_read_4b_aligned(src1);
        result = (int32_t)result_32bit;

        uint32_t after = 0;
        uint8_t amofunct = funct7 >> 4;
        switch (amofunct) {
        case 0b000:
          // amoadd
          after = result_32bit + src2;
          break;
        default:
          todo = true;
        }

        mem_write_4b_aligned(src1, after);
        dbg_log_memory(DBG_EVENT_ATOMIC, src1, 4, after);
      } else {
        // TODO: error out on misaligned atomics
        todo = true;
      }
    } else {
      todo = true;
    }
  }

  // reg write
  if (rd != 0) {
    hart.regfile[rd] = result;
  }

  // update pc
  if (do_jump) {
    dbg_log_branch(pc, jump_pc);
  }
  hart.pc = do_jump ? jump_pc : next_pc;

  n_retired++;
}

int main() {
  dbg_init();

  uint64_t dram_size = 256ul * 1024 * 1024;

  build_memory_map(dram_size);
  load_elf_to_physical_memory(
      "/usr/lib/riscv64-linux-gnu/opensbi/generic/fw_jump.elf");

  hart.pc = 0x1000;
  for (;;) {
    step();
  }
}
