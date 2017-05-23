#include <NTL/ZZ_pXFactoring.h>
#include <NTL/ZZ_pX.h>
#include <NTL/ZZ_pE.h>
#include <NTL/ZZ_p.h>
#include <NTL/ZZ.h>
#include <stdio.h>
#include <time.h>

#include "simple_benchmark.h"

using namespace std;
using namespace NTL;

typedef Vec<ZZ_p> FP2;

FP2 fp2Inv (FP2 a, ZZ p, ZZ n);

//--------------------------------


//n-way inversion function for batched fp^2 inversion
Vec<ZZ_pE> mont_n_way (Vec<FP2> vec, int n, ZZ p) {
	Vec<ZZ_pE> a;
	a.SetLength(n); //initialize vector of length n

	Vec<ZZ_pE> vec_pE = conv<Vec<ZZ_pE> >(conv<Vec<ZZ_pX> >(vec));
	a[0] = vec_pE[0]; //set a[0] to vec[0]

	//ZZ q = n;
	for (int j = 1; j < n; j++) {
		a[j] = a[j-1] * vec_pE[j];
	}

	//FP2 t = conv<FP2 >(a[n]);
	ZZ q = conv<ZZ>(2);
	ZZ_pE a_inv = conv<ZZ_pE> (conv<ZZ_pX> (fp2Inv (conv<FP2 >(conv<ZZ_pX>(a[n-1])), p, q)));

	for (int j = n - 1; j >= 1; j--) {
		a[j] = a_inv * a[j-1];
  	a_inv = a_inv * vec_pE[j];
  }

	a[0] = a_inv;
	return a;
}

Vec<FP2> partial_mont_n_way (Vec<FP2> vec, int n, ZZ p) {
	//FP2 -> ZZ_p	
	Vec<ZZ_p> t0; t0.SetLength(n);
	Vec<ZZ_p> t1; t1.SetLength(n);
	Vec<ZZ_p> den; den.SetLength(n);	

	for (int i = 0; i < n; i++) {
		power(t0[i], (vec[i])[0], 2);
		power(t1[i], (vec[i])[1], 2);
		den[i] = t0[i] + t1[i];
	}

	//batched ZZ_p inversion
	Vec<ZZ_p> a; a.SetLength(n);
	
	a[0] = den[0];
	for (int i = 1; i < n; i++) {
		a[i] = a[i-1] * den[i];
	}

	ZZ q = conv<ZZ>(2);
	ZZ_p a_inv = inv(a[n-1]);

	for (int i = n - 1; i >= 1; i--) {
		a[i] = a_inv * a[i-1];
  	a_inv = a_inv * den[i];
  }

	a[0] = a_inv;

	//ZZ_p -> FP2
	for (int i = 0; i < n; i++) {
		vec[i][0] = vec[i][0]*a[i];
		vec[i][1] = -vec[i][1]*a[i];
	}

	return vec;
}

//the following function belongs here only temporarily
//it is to be moved, when closer to completion, to PQC-SIDH

//assigns dest[0 ..n]
void fp2nwayinv751_mont(f2elm_t* vec, f2elm_t* dest, int n)
{// GF(p751^2) n-way partial-inversion
	int i;
	//f2elm_t -> felm_t	
	felm_t t0[n]; //t0.SetLength(n);
	felm_t t1[n]; //t1.SetLength(n);
	felm_t den[n]; //den.SetLength(n);

	for (i = 0; i < n; i++) {
		fpsqr751_mont((vec[i])[0], t0[i]); //t0[i] = a[i][0]^2
		fpsqr751_mont((vec[i])[1], t1[i]); //t1[i] = a[i][1]^2
		mp_add751(t0[i], t1[i], den[i]);//den[i] = t0[i] + t1[i];
		//need to use a mont function?
	}

	//batched ZZ_p inversion
	felm_t a[n]; //a.SetLength(n);
	
	fpcopy751(den[0], a[0]); //a[0] = den[0]

	for (i = 1; i < n; i++) {
		fpmul751_mont(a[i-1], den[i], a[i]); //a[i] = a[i-1] * den[i];
	}

	felm_t a_inv; // = inv(a[n-1]);
	fpcopy751(a[n-1], a_inv);
	fpinv751_mont(a_inv);
	//the current inversion function being used is constant time. we can use the function at line 445 (non constant time) with blinding to potentially achieve more iffecient inversion while maintaining security (testing required).

	for (i = n - 1; i >= 1; i--) {	
		fpmul751_mont(a_inv, a[i-1], a[i]); //a[i] = a_inv * a[i-1];
		fpmul751_mont(a[i], a_inv, a_inv); //a_inv = a_inv * den[i];
  }

	fpcopy751(a_inv, a[0]);	//a[0] = a_inv

	//ZZ_p -> FP2
	for (i = 0; i < n; i++) {
		fpmul751_mont(a[i], (vec[i])[0], (dest[i])[0]); //dest[i][0] = vec[i][0]*a[i];
		//NOTE: (vec[i])[1] should be -(vec[i])[1]
		fpmul751_mont(a[i], (vec[i])[1], (dest[i])[1]); //dest[i][1] = -vec[i][1]*a[i];
	}
}

//--------------------------------
void monInvPhaseA (ZZ* r, ZZ* k, ZZ a, ZZ p) {
	printf("monInvPhaseA called... \n"); //comment out print statements when benchmarking monInv
	ZZ u = p;
	ZZ v = a;
	ZZ s;
	s = 1;

	*r = conv<ZZ>(0);
	*k = conv<ZZ>(0);

	while (v > 0) {
		if (u % 2 == 0) {
			u = u>>1; //shiftright by 1
		} else if (v % 2 == 0) {
			v = v>>1; //shiftright by 1
			*r = 2*(*r);
		} else if (u > v) { //shiftright by 1
			u = (u-v)>>1; //shiftright by 1
			*r = *r+s;
			s = 2*s;
		} else if (v >= u) {
			v = (v-u)>>1; //shiftright by 1
			s = s+*r;
			*r = 2*(*r);
		}
		*k++;
	}

	if (*r >= p) {
		*r = *r - p;
	}

	*r = p - *r;
}

//--------------------------------

ZZ monInvPhaseB (ZZ r, ZZ k, ZZ n, ZZ p) {
	printf("monInvPhaseB called... \n"); //comment out print statements when benchmarking monInv
	ZZ i;
	ZZ q = k-n;
	for (i=1; i <= q; i++) {
		if (r % 2 == 0) {
			r = r>>1;		//shiftright by 1
		} else {
			r = (r+p)>>1;	//shiftright of r+p by 1
		}
	}

	return r;
}

//--------------------------------
ZZ monInv (ZZ a, ZZ p, ZZ n) {
	printf("monInv called... \n"); //comment out print statements when benchmarking monInv
	ZZ r;
	ZZ k;
	monInvPhaseA(&r, &k, a, p);
	ZZ x = monInvPhaseB(r, k, n, p);

	return x;
}

//--------------------------------

FP2 fp2Inv (FP2 a, ZZ p, ZZ n) {
	ZZ_p a0 = a[0]; // Re
	ZZ_p a1 = a[1]; // Im

	ZZ_p t0;
	ZZ_p t1;

	power(t0, a0, 2);
	power(t1, a1, 2);
	ZZ_p den = t0 + t1; //den := a0^2+a1^2;
	den = inv(den);

	//The following lines run the C++ implementation of Craig's 'monInv' Magma code
	// ZZ denZ = rep(den);
	// denZ = monInv(denZ,p,n);
	// den = conv<ZZ_p>(denZ);


	a[0]= a0*den;
	a[1] = -a1*den;
	return a;
}

int main (int argc, char** argv) {
	//get prime p input
	long psize;
	long err = 80;
	ZZ p;
	cout << "Enter prime modulus size: ";
	cin >> psize;
	p = GenPrime_ZZ(psize, err);	

	cout << "Chosen prime: " << p << "\n";

	int bsize;
	cout << "Enter batch size: ";
	cin >> bsize;

	//initialize fields
	ZZ_p::init(p);
	ZZ_pX initpX = ZZ_pX(INIT_MONO, 2) + ZZ_pX(INIT_MONO, 0);
	ZZ_pE::init(initpX);

	//set n to 2
	ZZ n = conv<ZZ>(2);

	Vec<FP2> vec;
	vec.SetLength(bsize);

	ZZ_p a;
	ZZ_p b;	
	for (int q = 0; q < bsize; q++) {
		vec[q].SetLength(2);
		a = random_ZZ_p();
		b = random_ZZ_p();
		vec[q][0] = a;
		vec[q][1] = b;
	}

	double start = get_time();
	Vec<ZZ_pE> batchinv;
	for (int i = 0; i < 1000; i++) {
		batchinv = mont_n_way (vec, bsize, p);
	}
	double diff = get_time() - start;

	cout << "Batched Inversion Execution Time: " << diff << "\n";

	start = get_time();
	Vec<FP2> partbatchinv;
	for (int i = 0; i < 1000; i++) {
		partbatchinv = partial_mont_n_way (vec, bsize, p);
	}
	diff = get_time() - start;

	cout << "Partial (ZZ_p) Batched Inversion Execution Time: " << diff << "\n";

	start = get_time();
	FP2 unbatchedinv;
	for (int i = 0; i < 1000; i++) {
		for (int j = 0; j < bsize; j++) {
			unbatchedinv = fp2Inv(vec[j], p, n);
		}
	}
	diff = get_time() - start;

	cout << "Unbatched Inversion Execution Time: " << diff << "\n";
	

	/*batched inversion tests -------------------------------------------
	Vec<FP2> vec;
	vec.SetLength(6);

	FP2 a_vec;
	a_vec.SetLength(2);
	cin >> a_vec;
	vec[0] = a_vec;

	FP2 a_vec2;
	a_vec.SetLength(2);
	cin >> a_vec2;
	vec[1] = a_vec2;
	
	FP2 a_vec3;
	a_vec.SetLength(2);
	cin >> a_vec3;
	vec[2] = a_vec3;

	FP2 a_vec4;
	a_vec.SetLength(2);
	cin >> a_vec4;
	vec[3] = a_vec4;

	FP2 a_vec5;
	a_vec.SetLength(2);
	cin >> a_vec5;
	vec[4] = a_vec5;

	FP2 a_vec6;
	a_vec.SetLength(2);
	cin >> a_vec6;
	vec[5] = a_vec6;

	Vec<FP2> batchinv = mont_n_way (vec, 6, p);
	cout << "Result from batch 0: " << batchinv[0] << "\n";
	cout << "Result from batch 1: " << batchinv[1] << "\n";
	cout << "Result from batch 2: " << batchinv[2] << "\n";
	cout << "Result from batch 3: " << batchinv[3] << "\n";
	cout << "Result from batch 4: " << batchinv[4] << "\n";
	cout << "Result from batch 5: " << batchinv[5] << "\n";
	
	FP2 inv;
	inv = fp2Inv (a_vec, p, n);
	cout << "Result from solo inversion 0: " << inv << "\n";
	inv = fp2Inv (a_vec2, p, n);
	cout << "Result from solo inversion 1: " << inv << "\n";
	inv = fp2Inv (a_vec3, p, n);
	cout << "Result from solo inversion 2: " << inv << "\n";
	inv = fp2Inv (a_vec4, p, n);
	cout << "Result from solo inversion 3: " << inv << "\n";
	inv = fp2Inv (a_vec5, p, n);
	cout << "Result from solo inversion 4: " << inv << "\n";
	inv = fp2Inv (a_vec6, p, n);
	cout << "Result from solo inversion 5: " << inv << "\n";
	/*-------------------------------------------------------------*/
	
	/*batched partial ZZ_p inversion test--------------------------
	Vec<FP2> vec;
	vec.SetLength(6);

	FP2 a_vec;
	a_vec.SetLength(2);
	cin >> a_vec;
	vec[0] = a_vec;

	FP2 a_vec2;
	a_vec.SetLength(2);
	cin >> a_vec2;
	vec[1] = a_vec2;
	
	FP2 a_vec3;
	a_vec.SetLength(2);
	cin >> a_vec3;
	vec[2] = a_vec3;

	FP2 a_vec4;
	a_vec.SetLength(2);
	cin >> a_vec4;
	vec[3] = a_vec4;

	FP2 a_vec5;
	a_vec.SetLength(2);
	cin >> a_vec5;
	vec[4] = a_vec5;

	FP2 a_vec6;
	a_vec.SetLength(2);
	cin >> a_vec6;
	vec[5] = a_vec6;

	Vec<FP2> batchinv = partial_mont_n_way (vec, 6, p);
	cout << "Result from batch 0: " << batchinv[0] << "\n";
	cout << "Result from batch 1: " << batchinv[1] << "\n";
	cout << "Result from batch 2: " << batchinv[2] << "\n";
	cout << "Result from batch 3: " << batchinv[3] << "\n";
	cout << "Result from batch 4: " << batchinv[4] << "\n";
	cout << "Result from batch 5: " << batchinv[5] << "\n";
	
	FP2 inv;
	inv = fp2Inv (a_vec, p, n);
	cout << "Result from solo inversion 0: " << inv << "\n";
	inv = fp2Inv (a_vec2, p, n);
	cout << "Result from solo inversion 1: " << inv << "\n";
	inv = fp2Inv (a_vec3, p, n);
	cout << "Result from solo inversion 2: " << inv << "\n";
	inv = fp2Inv (a_vec4, p, n);
	cout << "Result from solo inversion 3: " << inv << "\n";
	inv = fp2Inv (a_vec5, p, n);
	cout << "Result from solo inversion 4: " << inv << "\n";
	inv = fp2Inv (a_vec6, p, n);
	cout << "Result from solo inversion 5: " << inv << "\n";
	/*-------------------------------------------------------------*/

	/*benchmark tests (ZZ_pE inv vs. FP2 inv)------------------------
	FP2 a_vec;
	a_vec.SetLength(2);
	cin >> a_vec;	

	ZZ_pX a_pX = conv<ZZ_pX>(a_vec);
	ZZ_pE a_pE = conv<ZZ_pE>(a_pX);	

	double start = get_time();
	ZZ_pE inv_pE;
	for (int i = 0; i < 1000; i++) {
		inv_pE = inv(a_pE);
	}
	double diff = get_time() - start;

	cout << "Inversion in ZZ_pE: " << inv_pE << ", Execution time: " << diff << "\n";

	start = get_time();
	FP2 inv;
	for (int i = 0; i < 1000; i++) {
		inv = fp2Inv (a_vec, p, n);
	}
	diff = get_time() - start;

	cout << "Custom Inversion (ZZ_p): " << inv << ", Execution time: " << diff << "\n";
	----------------------------------------------------------------*/

	/*benchmark tests (batched inv vs. partial batched inv)---------
	Vec<FP2> vec;
	vec.SetLength(6);

	FP2 a_vec;
	a_vec.SetLength(2);
	cin >> a_vec;
	vec[0] = a_vec;

	FP2 a_vec2;
	a_vec.SetLength(2);
	cin >> a_vec2;
	vec[1] = a_vec2;
	
	FP2 a_vec3;
	a_vec.SetLength(2);
	cin >> a_vec3;
	vec[2] = a_vec3;

	FP2 a_vec4;
	a_vec.SetLength(2);
	cin >> a_vec4;
	vec[3] = a_vec4;

	FP2 a_vec5;
	a_vec.SetLength(2);
	cin >> a_vec5;
	vec[4] = a_vec5;

	FP2 a_vec6;
	a_vec.SetLength(2);
	cin >> a_vec6;
	vec[5] = a_vec6;	

	double start = get_time();
	Vec<ZZ_pE> batchinv;
	for (int i = 0; i < 1000; i++) {
		batchinv = mont_n_way (vec, 6, p);
	}
	double diff = get_time() - start;

	cout << "Batched Inversion Execution Time: " << diff << "\n";

	start = get_time();
	Vec<FP2> partbatchinv;
	for (int i = 0; i < 1000; i++) {
		partbatchinv = partial_mont_n_way (vec, 6, p);
	}
	diff = get_time() - start;

	cout << "Partial (ZZ_p) Batched Inversion Execution Time: " << diff << "\n";
	/*--------------------------------------------------------------*/

	return 0;
}

// douglas' benchmark reference
	// PRINT_TIMER_HEADER
	// TIME_OPERATION_SECONDS(inv = fp2Inv(a_vec, p, n), "fp2Inv", 1)
	// DEFINE_TIMER_VARIABLES
	// INITIALIZE_TIMER
	// START_TIMER
	// for (int i = 0; i < 1000; i++) {
	// 	inv_pE = inv(a_pE);
	// }
	// STOP_TIMER
	// FINALIZE_TIMER
	// PRINT_TIMER_AVG("ZZ_pE inv")
	// PRINT_TIMER_FOOTER
