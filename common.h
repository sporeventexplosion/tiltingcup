#ifndef TCUP_COMMON_H_
#define TCUP_COMMON_H_

#include <cassert>
#include <cstdint>
#include <cstring>
#include <vector>

typedef __int128 s128;
typedef unsigned __int128 u128;

struct MemoryMapEntry {
  uint64_t start, size;
  void *ptr;
};

struct Csr {
  // mie: 0x304, mip: 0x344 machine rw; warl, only legal values are stored in
  // this field
  uint16_t mie, mip;
  // mtvec: 0x305 machine rw
  uint64_t mtvec;
  // mscratch: 0x340 machine rw
  uint64_t mscratch;
  // pmpaddr0-pmpaddr63: 0x3b0-0x3ef machine rw
  uint64_t pmpaddrs[64];
  // mhpmcounter3-mhpmcounter31: 0xb03-0xb1f machine rw (first 3 entries unused)
  uint64_t mhpmcounters[32];
};

struct Hart {
  uint64_t regfile[32];
  uint64_t pc;
  Csr csr;
};

void build_memory_map(const char *reset_vec_addr, uint64_t dram_size);

void copy_to_physical_memory(const char *src, uint64_t start_addr,
                             uint64_t size);

void *mmap_whole_file_ro(const char *filepath, uint64_t *filelen);

void load_elf_to_physical_memory(const char *filepath);

void load_fdt_to_physical_memory(const char *filepath, uint64_t addr);

extern std::vector<MemoryMapEntry> memory_map;
extern char *dram;
extern Hart hart;

#endif
