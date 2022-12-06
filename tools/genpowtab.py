# Copyright 2022 Matt Rudary

# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at

#     http://www.apache.org/licenses/LICENSE-2.0

# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Generate the power tables used by bigint to parse decimal numbers."""

from math import ceil, log2
from pathlib import Path
import sys


WORD_LIMIT = 1010
BITS = 64
BASE = 1 << BITS


def print_power(p, f):
    print("  {", file=f)
    print("    {", file=f)
    size = 0
    while p:
        val = p % BASE
        p >>= BITS
        size += 1
        if val == 0:
            print("      0,", file=f)
        else:
            print(f"      0x{val:X}ull,", file=f)
    print("    },", file=f)
    print(f"    {size}", file=f)
    print("  },", file=f)


def main(f):
    p = 10**19
    print(f"""struct power_table_t {{
  std::uint64_t num[{WORD_LIMIT}];
  std::uint64_t size;
}};""", file=f)
    print("const power_table_t BI_DECIMAL_POWERS[] = {", file=f)
    while log2(p) < 64 * WORD_LIMIT:
        print_power(p, f)
        p *= p
    print("};", file=f)
    print(f"const std::uint64_t BI_DECIMAL_POWER_NEXT_SIZE = {ceil(log2(p) / 8)};",
          file=f)


if __name__ == '__main__':
    if len(sys.argv) > 1:
        p = Path(sys.argv[1])
        p.parent.mkdir(exist_ok=True, parents=True)
        with open(p, 'w') as f:
            main(f)
    else:
        main(sys.stdout)
