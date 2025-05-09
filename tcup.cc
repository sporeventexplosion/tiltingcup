#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>

const char *reg_names[32] = {
    "zero (x0)", "ra (x1)",  "sp (x2)",   "gp (x3)",   "tp (x4)",  "t0 (x5)",
    "t1 (x6)",   "t2 (x7)",  "s0 (x8)",   "s1 (x9)",   "a0 (x10)", "a1 (x11)",
    "a2 (x12)",  "a3 (x13)", "a4 (x14)",  "a5 (x15)",  "a6 (x16)", "a7 (x17)",
    "s2 (x18)",  "s3 (x19)", "s4 (x20)",  "s5 (x21)",  "s6 (x22)", "s7 (x23)",
    "s8 (x24)",  "s9 (x25)", "s10 (x26)", "s11 (x27)", "t3 (x28)", "t4 (x29)",
    "t5 (x30)",  "t6 (x31)",
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

struct Hart {
  uint64_t regfile[32];
  uint64_t pc;
};

Hart hart = {};

static int32_t decode_imm20_j_as_i32(uint32_t op) {
  int32_t ret = (int32_t)(op & 0x80000000u) >> 11;
  ret |= ((op & 0x7fe00000u) >> 20) | ((op & 0x100000) >> 9) | (op & 0xff000);
  return ret;
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

  bool use_cimm5 = false;

  uint64_t cimm5_sext64;
  if (compressed) {
    // expand compressed instructions
    uint8_t cmap = op & 3;
    uint8_t cfunct3 = (op >> 13) & 0x7;
    bool cbit12 = op & 0x1000;
    uint8_t crds1 = (op >> 7) & 0x1f;
    uint8_t crs2 = (op >> 2) & 0x1f;
    cimm5_sext64 = -((int64_t)(op >> 7) & 0x20) | ((op >> 2) & 0x1f);

    if (cmap == 0b00) {
      todo = true;
    } else if (cmap == 0b01) {
      switch (cfunct3) {
      case 0b010:
        // c.li, expands to addi, rd, x0, imm
        use_cimm5 = true;
        opc = 0b00100;
        funct3 = 0b000;
        rd = crds1;
        rs1 = 0;
        break;
      default:
        todo = true;
      }
    } else if (cmap == 0b10) {
      switch (cfunct3) {
      case 0b100:
        if (cbit12) {
          todo = true;
        } else {
          if (crs2 == 0) {
            if (crds1 == 0) {
              // TODO: this is reserved
              todo = true;
            } else {
              // c.jr, expands to jalr x0, 0(rs1)
              opc = 0b11001;
              funct3 = 0b000;
              rd = 0;
              rs1 = crds1;
            }
          } else {
            todo = true;
          }
        }
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
  }

  uint32_t imm20_u = op & -0x1000;
  uint16_t imm12_i_raw = op >> 20;
  uint64_t imm12_i_sext64 =
      compressed ? (use_cimm5 ? cimm5_sext64 : 0) : (int32_t)op >> 20;
  // already a multiple of two
  uint64_t imm20_j = decode_imm20_j_as_i32(op);

  // execute
  uint64_t pc = hart.pc;
  uint64_t next_pc = pc + (compressed ? 2 : 4);
  uint64_t src1 = hart.regfile[rs1];
  uint64_t src2 = hart.regfile[rs2];
  uint64_t result;

  bool do_load = false;
  uint64_t addr;

  bool do_jump = false;
  uint64_t jump_pc;

  switch (opc) {
  case 0b00000:
    do_load = true;
    switch (funct3) {
    case 0b011:
      // ld
      addr = src1 + imm12_i_sext64;
      break;
    default:
      todo = true;
    }
    break;

  case 0b00100:
    switch (funct3) {
    case 0b000:
      // addi
      result = src1 + imm12_i_sext64;
      break;
    default:
      todo = true;
    }
    break;

  case 0b00101:
    // auipc
    result = pc + imm20_u;
    break;

  case 0b01100: {
    if (funct7 & 0b1011111) {
      todo = true;
      break;
    }

    bool is_alt_func = funct7 == 0b0100000;
    switch (funct3) {
    case 0b000:
      result = is_alt_func ? src1 - src2 : src1 + src2;
      break;
    default:
      todo = true;
    }
    break;
  }

  case 0b11001:
    // jalr
    if (funct3 == 0b000) {
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
    jump_pc = pc + imm20_j;
    result = next_pc;
    break;

  case 0b11100:
    switch (funct3) {
    case 0b010:
      // csrrs
      // TODO
      if (rs1 != 0)
        todo = true;
      // TODO
      if (imm12_i_raw != 0xf14)
        todo = true; // mhartid csr
      result = 0;
      break;
    default:
      todo = true;
    }
    break;
  default:
    todo = true;
  }

  printf("pc = %lx\n", pc);
  if (todo) {
    char op_hex[9];
    if (compressed) {
      sprintf(op_hex, "%04x", (uint16_t)op);
    } else {
      sprintf(op_hex, "%08x", op);
    }
    fprintf(stderr, "TODO: pc = %lx, op = %s\n", pc, op_hex);
    fprintf(stderr, "Register state:\n");
    for (int i = 0; i < 32; i++) {
      uint64_t reg = hart.regfile[i];
      fprintf(stderr, "    %-12s0x%016lx  %ld\n", reg_names[i], reg, reg);
    }

    assert(false);
  }

  // memory
  if (do_load) {
    result = mem_read_8b_aligned(addr);
  }

  // reg write
  if (rd != 0) {
    hart.regfile[rd] = result;
  }
  // update pc
  hart.pc = do_jump ? jump_pc : next_pc;
}

int main() {
  uint64_t dram_size = 256ul * 1024 * 1024;

  build_memory_map(dram_size);
  load_elf_to_physical_memory(
      "/usr/lib/riscv64-linux-gnu/opensbi/generic/fw_jump.elf");

  hart.pc = 0x1000;
  for (;;) {
    step();
  }
}
