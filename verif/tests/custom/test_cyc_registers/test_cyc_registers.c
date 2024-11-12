/*
**
** Copyright 2020 OpenHW Group
**
** Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
**
**     https://solderpad.org/licenses/
**
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
**
*/

#include <stdint.h>
#include <stdio.h>
#include "encoding.h"

int main(int argc, char* arg[]) {
	uint64_t starting_cyc = read_csr(0xc00);
	uint64_t starting_cyc0= read_csr(0x7C4);

	uint32_t enabled = 1;
	uint32_t selected = 0;
	uint32_t status = (enabled << 16) | selected;
	write_csr(0x7C3, status);
	printf("%d: Hello World !", 0);

	enabled = 2;
	selected = 1;
	status = (enabled << 16) | selected;
	write_csr(0x7C3, status);
	uint64_t ending_cyc1 = read_csr(0x7C4);
	//printf("cyc:%d,\ncyc_0:%d,\nend_cyc1:%d\n",starting_cyc,starting_cyc0, ending_cyc1);
	int a = 0;
	for (int i = 0; i < 5; i++)
	{
		a += i;
	}

	return 0;
}
