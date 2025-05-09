#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>

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

struct Hart {
  uint64_t regfile[32];
  uint64_t pc;
};

Hart hart = {};

void step() {
  bool todo = false;

  // fetch
  uint32_t op = mem_read_4b_aligned(hart.pc);
  // decode
  // TODO: C extension
  if ((op & 3) != 3)
    todo = true;

  uint8_t opc = (op >> 2) & 0x1f;
  uint8_t funct3 = (op >> 12) & 0x7;
  uint8_t rd = (op >> 7) & 0x1f;
  uint8_t rs1 = (op >> 15) & 0x1f;

  uint32_t imm20_upper = op & -0x1000;
  uint64_t imm12_i = op >> 20;
  uint64_t imm12_i_sext64 = (int32_t)op >> 20;

  // execute
  uint64_t pc = hart.pc;
  uint64_t next_pc = pc + 4;
  uint64_t src1 = hart.regfile[rs1];
  uint64_t result;

  bool do_load = false;
  uint64_t addr;

  bool do_jump = false;
  uint64_t jump_pc;

  switch (opc) {
  case 0b00000:
    do_load = true;
    switch (funct3) {
    case 0b011: // ld
      addr = src1 + imm12_i_sext64;
      break;
    default:
      todo = true;
    }
    break;

  case 0b00100:
    switch (funct3) {
    case 0b000: // addi
      result = src1 + imm12_i_sext64;
      break;
    default:
      todo = true;
    }
    break;

  case 0b00101: // auipc
    result = pc + imm20_upper;
    break;

  case 0b11001: // jalr
    if (funct3 == 0b000) {
      do_jump = true;
      jump_pc = (src1 + imm12_i_sext64) & -0x2;
      result = next_pc;
    } else {
      todo = true;
    }
    break;

  case 0b11100:
    switch (funct3) {
    case 0b010: // csrrs
      // TODO
      if (rs1 != 0)
        todo = true;
      // TODO
      if (imm12_i != 0xf14)
        todo = true; // mhartid csr
      result = 0;
      break;
    default:
      todo = true;
    }
    break;
    break;
  default:
    todo = true;
  }

  if (todo) {
    fprintf(stderr, "pc = %lx, op = %08x\n", hart.pc, op);
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
