// FAST_MOD.cpp : 此文件包含 "main" 函数。程序执行将在此处开始并结束。
//

#include <iostream>
#include <intrin.h>

const size_t all_zeros = 0ULL;
const size_t all_ones = ~all_zeros;

__inline bool printbin(size_t value, bool skip_lzs = false, bool pad_space = false) {
	bool any = false;
	bool lz = true;
	for (int i = 63; i >= 0; i--) {
		size_t mask = 1ULL << i;
		if (skip_lzs && lz && (value & mask) == 0) {
			if (pad_space) printf(" ");
			continue;
		}
		printf(value & mask ? "1" : "0");
		any = true;
		if (value & mask) lz = false;
	}
	return any;
}
__inline void printbin(size_t* value, int length, bool skip_lzs = false, bool pad_space = false) {
	bool any = true;
	for (int i = length - 1; i >= 0; i--) {
		any = printbin(value[i], any && skip_lzs,
			(i == length - 1) && pad_space);
	}
}
__inline void printhex(size_t* value, int length) {
	for (int i = length * 8 - 1; i >= 0; i--) {
		printf("%02X", *((unsigned char*)value) + i);
	}
}

__inline size_t* generate(size_t* bn, int length) {
	size_t v = 0;
	int p = 0;
	while (p < length) {
		_rdrand64_step(&v);
		bn[p++] = v;
	}
	return bn;
}
__inline int _msb_u64(size_t n) {
	return 64 - (int)_lzcnt_u64(n);
}
__inline int _msb_u64(size_t* bn, int length) {
	if (length == 0) return all_zeros;
	int count = 64;
	int p = length;
	while (count == 64 && --p >= 0) {
		count = (int)_lzcnt_u64(bn[p]);
	}
	return p < 0 ? 0 : ((p) << 6) + (63 - (count % 64));
}

__inline void sub_core(size_t* result, size_t* a, size_t* b, int nbits) {
	//a-b
	size_t borrow = all_zeros;
	for (int i = 0; i < nbits; i++) {
		if (borrow != all_zeros) {
			if (result[i] == all_zeros) {
				//keep borrow and set all1s
				result[i] = all_ones;
			}
			else {
				result[i] -= borrow;
				borrow = all_zeros;
			}
		}
		if (a[i] >= b[i]) {
			result[i] = a[i] - b[i];
			borrow = all_zeros;
		}
		else { //borrow
			result[i] = (all_ones - a[i]) + b[i];
			borrow = all_zeros;
			++borrow;
		}
	}

}
__inline size_t get_bits(size_t* a, int max_pos, int basepos, int length = 64) {
	if (basepos > max_pos)
		basepos = 64 - basepos;
	int drem = basepos % 64;
	int dcount = (basepos >> 6);
	int exceeding = max_pos - (basepos + 64);
	size_t value =
		drem == 0
		? (a[dcount + 0])
		: ((a[dcount + 1] << (64 - drem)))
		| (a[dcount + 0] >> drem)
		;

	if (exceeding < 0) {
		value &= (all_ones >> -exceeding);
	}
	//0-64
	length = length < 0 ? 0 : length;
	length = length > 64 ? 64 : length;
	return length == 64 ? value : value & ~(all_ones << length);
}
__inline size_t set_bits(size_t* a, int maxpos, int bp, size_t value, int length = 64) {
	int drem = bp % 64;
	int dcount = (bp >> 6);
	int exceeding = maxpos - (bp + 64);
	int ecount = 0;
	int erem = 0;
	if (exceeding < 0) {
		exceeding = -exceeding;
		ecount = exceeding >> 6;
		erem = exceeding % 64;
		value &= (all_ones >> erem);
	}
	if (drem == 0)
	{
		a[dcount + 0] = (a[dcount + 0] & ~(all_ones << erem)) | value;
	}
	else {
		size_t v0 = value << drem;
		size_t a0 = a[dcount + 0] & ~(all_ones << drem);

		size_t v1 = value >> (64 - drem);
		size_t a1 = a[dcount + 1] & (all_ones << drem);
		if (erem != 0) {
			if (ecount == 0)
				a0 &= ~(all_ones >> erem);
			else
				a1 &= ~(all_ones >> erem);
		}
		a[dcount + 0] = v0 | a0;
		if ((dcount + 1) * 64 < maxpos) {
			a[dcount + 1] = v1 | a1;
		}
	}
	return value;
}

__inline int copybits(void* dst, void* src, int length) {
	if (dst != 0 && src != 0) {
		int rs = length % 64;
		int ps = length >> 6;
		if (ps > 0) {
			memcpy(dst, src, (size_t)ps << 3);
		}
		*((size_t*)dst + ps) =
			(*(size_t*)src + ps) & ~(all_ones << rs)
			;
		return length;
	}
	return 0;
}
__inline int sub_core_shift_bits(size_t* result, size_t* a, size_t* b, int rbits, int abits, int bbits) {
	size_t borrow = 0;
	int delta = abits - bbits;
	if (delta < 0) return delta;
	//for every pa rt in b
	//[aaaaaaaaa]
	//[....bbbbb]
	//
	size_t rx = all_zeros;
	copybits(result, a, delta);
	bool any = false;
	for (int i = 0; i < bbits; i += 64) {
		size_t ax = get_bits(a, abits, i + delta);
		size_t bx = get_bits(b, bbits, i);

		if (borrow != all_zeros) {
			if (rx == all_zeros) {
				//keep borrow and set all1s
				rx = all_ones;
			}
			else {
				rx -= borrow;
				borrow = all_zeros;
			}
		}
		if (ax >= bx) {
			rx = ax - bx;
			borrow = all_zeros;
		}
		else { //borrow
			rx = (all_ones - ax) + bx;
			borrow = all_zeros;
			++borrow;
		}
		any |= rx != 0;
		set_bits(result, rbits, i + delta, rx);
	}
	return delta == 0 ? (any ? -1 : 0) : delta;
}

__inline int max_sub(size_t* result, size_t* a, size_t* b, int a_length, int b_length) {
	int abits = _msb_u64(a, a_length);
	int bbits = _msb_u64(b, b_length);
	int delta = abits - bbits;
	return delta < 0
		? -1
		: sub_core_shift_bits(result, a, b, (a_length << 6), abits, bbits)
		;
}
int fast_mod(size_t* result, size_t* minuend, size_t* subtrahend, int minuend_length, int subtrahend_length) {
	int cmp = 1;
	memset(result, 0, (size_t)minuend_length << 3);
	while (true)
	{
		cmp = max_sub(result, minuend, subtrahend, minuend_length, subtrahend_length);
		if (cmp <= 0) break;
		memcpy(minuend, result, (size_t)minuend_length << 3);
	}

	return cmp;
}
int subrange_sample() {
	const int a_length = 192 / 64; //32
	size_t result[a_length] = { 0 };
	size_t a[a_length] = { 0 };
	generate(a, a_length);
	printf("a: ");
	printbin(a, a_length);
	printf("\n");
	//example
	int any;
	const int start = 64;
	for (int i = start; i < (a_length << 6) - 1; i++) {
		size_t ax = get_bits(a, a_length << 6, i);
		printf("ax:");
		any = 0;
		for (int j = start; j < ((a_length << 6) - i); j++) {
			printf(" ");
			any = 1;
		}
		printbin(ax);
		printf("\n");
		if (!any) break;
	}
	return 0;
}
int fastmod_sample() {
	const int a_length = 2048 / 64; //32
	const int b_length = a_length >> 1;

	size_t result[a_length] = { 0 };
	size_t a[a_length] = { 0 };
	size_t b[b_length] = { 0 };

	generate(a, a_length);
	generate(b, b_length);
	//a[1] = 0b0000000011100011100101110110100001100001101001001010110000101000;
	//a[0] = 0b0110110001101111110100100100000110011011110010110000000100110010;
	//b[0] = 0b0000000000000000001010001111010110010011110111111100110011011101;

	printf("a:%d\n", _msb_u64(a, a_length));
	printbin(a, a_length);
	printf("\n");
	printf("b:%d\n", _msb_u64(b, b_length));
	printbin(b, b_length);
	printf("\n");

	int r = fast_mod(result, a, b, a_length, b_length);
	if (r == 0) {
		printf("a %% b = 0\n");
		printbin(result, a_length);
		printf("\n");
	}
	else {
		printf("a %% b = ");
		printbin(result, a_length);
		printf("\n    b = ");
		for (int i = 0; i < b_length << 6; i++) printf("0");
		printbin(b, b_length);
		printf("\n");
	}
	return 0;
}
int main()
{
	//subrange_sample();
	fastmod_sample();
	return 0;
}
