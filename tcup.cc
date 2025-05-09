#include <cassert>
#include <cstdint>
#include <cstdio>
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

  fprintf(stderr, "pc = %lx\n", hart.pc);
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

  hart.pc = 0x1000;
  build_memory_map(dram_size);

  for (;;) {
    step();
  }
}
