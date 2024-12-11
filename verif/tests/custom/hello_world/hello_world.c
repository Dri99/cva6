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

int stack[1000];

int main(int argc, char* arg[]) {
	printf("Initial cycles:%lu\n",read_csr(mcycle));
	printf("Initial instr:%lu\n",read_csr(minstret));
	printf("%d: Hello World !", 0);
	
	for(int i=0; i<1000;i++){
		stack[i] = 0xaaaa;
	}
	
	printf("Final cycles:%lu\n",read_csr(mcycle));
	printf("Final instr:%lu\n",read_csr(minstret));
}
