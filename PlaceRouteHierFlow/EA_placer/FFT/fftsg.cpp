///////////////////////////////////////////////////////////////////////////////
// BSD 3-Clause License
//
// Copyright (c) 2018-2020, The Regents of the University of California
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//
// * Redistributions of source code must retain the above copyright notice, this
//   list of conditions and the following disclaimer.
//
// * Redistributions in binary form must reproduce the above copyright notice,
//   this list of conditions and the following disclaimer in the documentation
//   and/or other materials provided with the distribution.
//
// * Neither the name of the copyright holder nor the names of its
//   contributors may be used to endorse or promote products derived from
//   this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE
// DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
// FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
// DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
// SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
// CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
// OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
///////////////////////////////////////////////////////////////////////////////

/*
Fast Fourier/Cosine/Sine Transform
    dimension   :one
    data length :power of 2
    decimation  :frequency
    radix       :split-radix
    data        :inplace
    table       :use
functions
    cdft: Complex Discrete Fourier Transform
    rdft: Real Discrete Fourier Transform
    ddct: Discrete Cosine Transform
    ddst: Discrete Sine Transform
    dfct: Cosine Transform of RDFT (Real Symmetric DFT)
    dfst: Sine Transform of RDFT (Real Anti-symmetric DFT)
function prototypes
    void cdft(int, int, float   *, int *, float   *);
    void rdft(int, int, float   *, int *, float   *);
    void ddct(int, int, float   *, int *, float   *);
    void ddst(int, int, float   *, int *, float   *);
    void dfct(int, float   *, float   *, int *, float   *);
    void dfst(int, float   *, float   *, int *, float   *);
macro definitions
    USE_CDFT_PTHREADS : default=not defined
        CDFT_THREADS_BEGIN_N  : must be >= 512, default=8192
        CDFT_4THREADS_BEGIN_N : must be >= 512, default=65536
    USE_CDFT_WINTHREADS : default=not defined
        CDFT_THREADS_BEGIN_N  : must be >= 512, default=32768
        CDFT_4THREADS_BEGIN_N : must be >= 512, default=524288


-------- Complex DFT (Discrete Fourier Transform) --------
    [definition]
        <case1>
            X[k] = sum_j=0^n-1 x[j]*exp(2*pi*i*j*k/n), 0<=k<n
        <case2>
            X[k] = sum_j=0^n-1 x[j]*exp(-2*pi*i*j*k/n), 0<=k<n
        (notes: sum_j=0^n-1 is a summation from j=0 to n-1)
    [usage]
        <case1>
            ip[0] = 0; // first time only
            cdft(2*n, 1, a, ip, w);
        <case2>
            ip[0] = 0; // first time only
            cdft(2*n, -1, a, ip, w);
    [parameters]
        2*n            :data length (int)
                        n >= 1, n = power of 2
        a[0...2*n-1]   :input/output data (float   *)
                        input data
                            a[2*j] = Re(x[j]),
                            a[2*j+1] = Im(x[j]), 0<=j<n
                        output data
                            a[2*k] = Re(X[k]),
                            a[2*k+1] = Im(X[k]), 0<=k<n
        ip[0...*]      :work area for bit reversal (int *)
                        length of ip >= 2+sqrt(n)
                        strictly,
                        length of ip >=
                            2+(1<<(int)(log(n+0.5)/log(2))/2).
                        ip[0],ip[1] are pointers of the cos/sin table.
        w[0...n/2-1]   :cos/sin table (float   *)
                        w[],ip[] are initialized if ip[0] == 0.
    [remark]
        Inverse of
            cdft(2*n, -1, a, ip, w);
        is
            cdft(2*n, 1, a, ip, w);
            for (j = 0; j <= 2 * n - 1; j++) {
                a[j] *= 1.0 / n;
            }
        .


-------- Real DFT / Inverse of Real DFT --------
    [definition]
        <case1> RDFT
            R[k] = sum_j=0^n-1 a[j]*cos(2*pi*j*k/n), 0<=k<=n/2
            I[k] = sum_j=0^n-1 a[j]*sin(2*pi*j*k/n), 0<k<n/2
        <case2> IRDFT (excluding scale)
            a[k] = (R[0] + R[n/2]*cos(pi*k))/2 +
                   sum_j=1^n/2-1 R[j]*cos(2*pi*j*k/n) +
                   sum_j=1^n/2-1 I[j]*sin(2*pi*j*k/n), 0<=k<n
    [usage]
        <case1>
            ip[0] = 0; // first time only
            rdft(n, 1, a, ip, w);
        <case2>
            ip[0] = 0; // first time only
            rdft(n, -1, a, ip, w);
    [parameters]
        n              :data length (int)
                        n >= 2, n = power of 2
        a[0...n-1]     :input/output data (float   *)
                        <case1>
                            output data
                                a[2*k] = R[k], 0<=k<n/2
                                a[2*k+1] = I[k], 0<k<n/2
                                a[1] = R[n/2]
                        <case2>
                            input data
                                a[2*j] = R[j], 0<=j<n/2
                                a[2*j+1] = I[j], 0<j<n/2
                                a[1] = R[n/2]
        ip[0...*]      :work area for bit reversal (int *)
                        length of ip >= 2+sqrt(n/2)
                        strictly,
                        length of ip >=
                            2+(1<<(int)(log(n/2+0.5)/log(2))/2).
                        ip[0],ip[1] are pointers of the cos/sin table.
        w[0...n/2-1]   :cos/sin table (float   *)
                        w[],ip[] are initialized if ip[0] == 0.
    [remark]
        Inverse of
            rdft(n, 1, a, ip, w);
        is
            rdft(n, -1, a, ip, w);
            for (j = 0; j <= n - 1; j++) {
                a[j] *= 2.0 / n;
            }
        .


-------- DCT (Discrete Cosine Transform) / Inverse of DCT --------
    [definition]
        <case1> IDCT (excluding scale)
            C[k] = sum_j=0^n-1 a[j]*cos(pi*j*(k+1/2)/n), 0<=k<n
        <case2> DCT
            C[k] = sum_j=0^n-1 a[j]*cos(pi*(j+1/2)*k/n), 0<=k<n
    [usage]
        <case1>
            ip[0] = 0; // first time only
            ddct(n, 1, a, ip, w);
        <case2>
            ip[0] = 0; // first time only
            ddct(n, -1, a, ip, w);
    [parameters]
        n              :data length (int)
                        n >= 2, n = power of 2
        a[0...n-1]     :input/output data (float   *)
                        output data
                            a[k] = C[k], 0<=k<n
        ip[0...*]      :work area for bit reversal (int *)
                        length of ip >= 2+sqrt(n/2)
                        strictly,
                        length of ip >=
                            2+(1<<(int)(log(n/2+0.5)/log(2))/2).
                        ip[0],ip[1] are pointers of the cos/sin table.
        w[0...n*5/4-1] :cos/sin table (float   *)
                        w[],ip[] are initialized if ip[0] == 0.
    [remark]
        Inverse of
            ddct(n, -1, a, ip, w);
        is
            a[0] *= 0.5;
            ddct(n, 1, a, ip, w);
            for (j = 0; j <= n - 1; j++) {
                a[j] *= 2.0 / n;
            }
        .


-------- DST (Discrete Sine Transform) / Inverse of DST --------
    [definition]
        <case1> IDST (excluding scale)
            S[k] = sum_j=1^n A[j]*sin(pi*j*(k+1/2)/n), 0<=k<n
        <case2> DST
            S[k] = sum_j=0^n-1 a[j]*sin(pi*(j+1/2)*k/n), 0<k<=n
    [usage]
        <case1>
            ip[0] = 0; // first time only
            ddst(n, 1, a, ip, w);
        <case2>
            ip[0] = 0; // first time only
            ddst(n, -1, a, ip, w);
    [parameters]
        n              :data length (int)
                        n >= 2, n = power of 2
        a[0...n-1]     :input/output data (float   *)
                        <case1>
                            input data
                                a[j] = A[j], 0<j<n
                                a[0] = A[n]
                            output data
                                a[k] = S[k], 0<=k<n
                        <case2>
                            output data
                                a[k] = S[k], 0<k<n
                                a[0] = S[n]
        ip[0...*]      :work area for bit reversal (int *)
                        length of ip >= 2+sqrt(n/2)
                        strictly,
                        length of ip >=
                            2+(1<<(int)(log(n/2+0.5)/log(2))/2).
                        ip[0],ip[1] are pointers of the cos/sin table.
        w[0...n*5/4-1] :cos/sin table (float   *)
                        w[],ip[] are initialized if ip[0] == 0.
    [remark]
        Inverse of
            ddst(n, -1, a, ip, w);
        is
            a[0] *= 0.5;
            ddst(n, 1, a, ip, w);
            for (j = 0; j <= n - 1; j++) {
                a[j] *= 2.0 / n;
            }
        .


-------- Cosine Transform of RDFT (Real Symmetric DFT) --------
    [definition]
        C[k] = sum_j=0^n a[j]*cos(pi*j*k/n), 0<=k<=n
    [usage]
        ip[0] = 0; // first time only
        dfct(n, a, t, ip, w);
    [parameters]
        n              :data length - 1 (int)
                        n >= 2, n = power of 2
        a[0...n]       :input/output data (float   *)
                        output data
                            a[k] = C[k], 0<=k<=n
        t[0...n/2]     :work area (float   *)
        ip[0...*]      :work area for bit reversal (int *)
                        length of ip >= 2+sqrt(n/4)
                        strictly,
                        length of ip >=
                            2+(1<<(int)(log(n/4+0.5)/log(2))/2).
                        ip[0],ip[1] are pointers of the cos/sin table.
        w[0...n*5/8-1] :cos/sin table (float   *)
                        w[],ip[] are initialized if ip[0] == 0.
    [remark]
        Inverse of
            a[0] *= 0.5;
            a[n] *= 0.5;
            dfct(n, a, t, ip, w);
        is
            a[0] *= 0.5;
            a[n] *= 0.5;
            dfct(n, a, t, ip, w);
            for (j = 0; j <= n; j++) {
                a[j] *= 2.0 / n;
            }
        .


-------- Sine Transform of RDFT (Real Anti-symmetric DFT) --------
    [definition]
        S[k] = sum_j=1^n-1 a[j]*sin(pi*j*k/n), 0<k<n
    [usage]
        ip[0] = 0; // first time only
        dfst(n, a, t, ip, w);
    [parameters]
        n              :data length + 1 (int)
                        n >= 2, n = power of 2
        a[0...n-1]     :input/output data (float   *)
                        output data
                            a[k] = S[k], 0<k<n
                        (a[0] is used for work area)
        t[0...n/2-1]   :work area (float   *)
        ip[0...*]      :work area for bit reversal (int *)
                        length of ip >= 2+sqrt(n/4)
                        strictly,
                        length of ip >=
                            2+(1<<(int)(log(n/4+0.5)/log(2))/2).
                        ip[0],ip[1] are pointers of the cos/sin table.
        w[0...n*5/8-1] :cos/sin table (float   *)
                        w[],ip[] are initialized if ip[0] == 0.
    [remark]
        Inverse of
            dfst(n, a, t, ip, w);
        is
            dfst(n, a, t, ip, w);
            for (j = 1; j <= n - 1; j++) {
                a[j] *= 2.0 / n;
            }
        .


Appendix :
    The cos/sin table is recalculated when the larger table required.
    w[] and ip[] are compatible with all routines.
*/

#include <cmath>
#include <iostream>

namespace replace {

void ddct(int n, int isgn, float *a, int *ip, float *w) {
  void makewt(int nw, int *ip, float *w);
  void makect(int nc, int *ip, float *c);
  void cftfsub(int n, float *a, int *ip, int nw, float *w);
  void cftbsub(int n, float *a, int *ip, int nw, float *w);
  void rftfsub(int n, float *a, int nc, float *c);
  void rftbsub(int n, float *a, int nc, float *c);
  void dctsub(int n, float *a, int nc, float *c);
  int j, nw, nc;
  float xr;

  nw = ip[0];
  if (n > (nw << 2)) {
    nw = n >> 2;
    makewt(nw, ip, w);
  }
  nc = ip[1];
  if (n > nc) {
    nc = n;
    makect(nc, ip, w + nw);
  }
  if (isgn < 0) {
    xr = a[n - 1];

    for (j = n - 2; j >= 2; j -= 2) {
      a[j + 1] = a[j] - a[j - 1];
      a[j] += a[j - 1];
    }
    a[1] = a[0] - xr;
    a[0] += xr;
    if (n > 4) {
      rftbsub(n, a, nc, w + nw);
      cftbsub(n, a, ip, nw, w);
    } else if (n == 4) {
      cftbsub(n, a, ip, nw, w);
    }
  }
  dctsub(n, a, nc, w + nw);
  if (isgn >= 0) {
    if (n > 4) {
      cftfsub(n, a, ip, nw, w);
      rftfsub(n, a, nc, w + nw);
    } else if (n == 4) {
      cftfsub(n, a, ip, nw, w);
    }
    xr = a[0] - a[1];
    a[0] += a[1];
    for (j = 2; j < n; j += 2) {
      a[j - 1] = a[j] - a[j + 1];
      a[j] += a[j + 1];
    }
    a[n - 1] = xr;
  }
}

void ddst(int n, int isgn, float *a, int *ip, float *w) {
  void makewt(int nw, int *ip, float *w);
  void makect(int nc, int *ip, float *c);
  void cftfsub(int n, float *a, int *ip, int nw, float *w);
  void cftbsub(int n, float *a, int *ip, int nw, float *w);
  void rftfsub(int n, float *a, int nc, float *c);
  void rftbsub(int n, float *a, int nc, float *c);
  void dstsub(int n, float *a, int nc, float *c);
  int j, nw, nc;
  float xr;

  nw = ip[0];
  if (n > (nw << 2)) {
    nw = n >> 2;
    makewt(nw, ip, w);
  }
  nc = ip[1];
  if (n > nc) {
    nc = n;
    makect(nc, ip, w + nw);
  }
  if (isgn < 0) {
    xr = a[n - 1];
    for (j = n - 2; j >= 2; j -= 2) {
      a[j + 1] = -a[j] - a[j - 1];
      a[j] -= a[j - 1];
    }
    a[1] = a[0] + xr;
    a[0] -= xr;
    if (n > 4) {
      rftbsub(n, a, nc, w + nw);
      cftbsub(n, a, ip, nw, w);
    } else if (n == 4) {
      cftbsub(n, a, ip, nw, w);
    }
  }
  dstsub(n, a, nc, w + nw);
  if (isgn >= 0) {
    if (n > 4) {
      cftfsub(n, a, ip, nw, w);
      rftfsub(n, a, nc, w + nw);
    } else if (n == 4) {
      cftfsub(n, a, ip, nw, w);
    }
    xr = a[0] - a[1];
    a[0] += a[1];
    for (j = 2; j < n; j += 2) {
      a[j - 1] = -a[j] - a[j + 1];
      a[j] -= a[j + 1];
    }
    a[n - 1] = -xr;
  }
}

/* -------- initializing routines -------- */

void makewt(int nw, int *ip, float *w) {
  void makeipt(int nw, int *ip);
  int j, nwh, nw0, nw1;
  float delta, wn4r, wk1r, wk1i, wk3r, wk3i;

  ip[0] = nw;
  ip[1] = 1;
  if (nw > 2) {
    nwh = nw >> 1;
    delta = atan(1.0) / nwh;
    wn4r = cos(delta * nwh);
    w[0] = 1;
    w[1] = wn4r;
    if (nwh == 4) {
      w[2] = cos(delta * 2);
      w[3] = sin(delta * 2);
    } else if (nwh > 4) {
      makeipt(nw, ip);
      w[2] = 0.5 / cos(delta * 2);
      w[3] = 0.5 / cos(delta * 6);
      for (j = 4; j < nwh; j += 4) {
        w[j] = cos(delta * j);
        w[j + 1] = sin(delta * j);
        w[j + 2] = cos(3 * delta * j);
        w[j + 3] = -sin(3 * delta * j);
      }
    }
    nw0 = 0;
    while (nwh > 2) {
      nw1 = nw0 + nwh;
      nwh >>= 1;
      w[nw1] = 1;
      w[nw1 + 1] = wn4r;
      if (nwh == 4) {
        wk1r = w[nw0 + 4];
        wk1i = w[nw0 + 5];
        w[nw1 + 2] = wk1r;
        w[nw1 + 3] = wk1i;
      } else if (nwh > 4) {
        wk1r = w[nw0 + 4];
        wk3r = w[nw0 + 6];
        w[nw1 + 2] = 0.5 / wk1r;
        w[nw1 + 3] = 0.5 / wk3r;
        for (j = 4; j < nwh; j += 4) {
          wk1r = w[nw0 + 2 * j];
          wk1i = w[nw0 + 2 * j + 1];
          wk3r = w[nw0 + 2 * j + 2];
          wk3i = w[nw0 + 2 * j + 3];
          w[nw1 + j] = wk1r;
          w[nw1 + j + 1] = wk1i;
          w[nw1 + j + 2] = wk3r;
          w[nw1 + j + 3] = wk3i;
        }
      }
      nw0 = nw1;
    }
  }
}

void makeipt(int nw, int *ip) {
  int j, l, m, m2, p, q;

  ip[2] = 0;
  ip[3] = 16;
  m = 2;
  for (l = nw; l > 32; l >>= 2) {
    m2 = m << 1;
    q = m2 << 3;
    for (j = m; j < m2; j++) {
      p = ip[j] << 2;
      ip[m + j] = p;
      ip[m2 + j] = p + q;
    }
    m = m2;
  }
}

void makect(int nc, int *ip, float *c) {
  int j, nch;
  float delta;

  ip[1] = nc;
  if (nc > 1) {
    nch = nc >> 1;
    delta = atan(1.0) / nch;
    c[0] = cos(delta * nch);
    c[nch] = 0.5 * c[0];
    for (j = 1; j < nch; j++) {
      c[j] = 0.5 * cos(delta * j);
      c[nc - j] = 0.5 * sin(delta * j);
    }
  }
}

/* -------- child routines -------- */

#ifdef USE_CDFT_PTHREADS
#define USE_CDFT_THREADS
#ifndef CDFT_THREADS_BEGIN_N
#define CDFT_THREADS_BEGIN_N 8192
#endif
#ifndef CDFT_4THREADS_BEGIN_N
#define CDFT_4THREADS_BEGIN_N 65536
#endif
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#define cdft_thread_t pthread_t
#define cdft_thread_create(thp, func, argp)                   \
  {                                                           \
    if (pthread_create(thp, NULL, func, (void *)argp) != 0) { \
      fprintf(stderr, "cdft thread error\n");                 \
      exit(1);                                                \
    }                                                         \
  }
#define cdft_thread_wait(th)                  \
  {                                           \
    if (pthread_join(th, NULL) != 0) {        \
      fprintf(stderr, "cdft thread error\n"); \
      exit(1);                                \
    }                                         \
  }
#endif /* USE_CDFT_PTHREADS */

#ifdef USE_CDFT_WINTHREADS
#define USE_CDFT_THREADS
#ifndef CDFT_THREADS_BEGIN_N
#define CDFT_THREADS_BEGIN_N 32768
#endif
#ifndef CDFT_4THREADS_BEGIN_N
#define CDFT_4THREADS_BEGIN_N 524288
#endif
#include <stdio.h>
#include <stdlib.h>
#include <windows.h>
#define cdft_thread_t HANDLE
#define cdft_thread_create(thp, func, argp)                                               \
  {                                                                                       \
    DWORD thid;                                                                           \
    *(thp) = CreateThread(NULL, 0, (LPTHREAD_START_ROUTINE)func, (LPVOID)argp, 0, &thid); \
    if (*(thp) == 0) {                                                                    \
      fprintf(stderr, "cdft thread error\n");                                             \
      exit(1);                                                                            \
    }                                                                                     \
  }
#define cdft_thread_wait(th)           \
  {                                    \
    WaitForSingleObject(th, INFINITE); \
    CloseHandle(th);                   \
  }
#endif /* USE_CDFT_WINTHREADS */

void cftfsub(int n, float *a, int *ip, int nw, float *w) {
  void bitrv208(float *a);
  void cftf081(float *a, float *w);

  if (n > 8) {
    cftf081(a, w);
    bitrv208(a);
  }
}

void cftbsub(int n, float *a, int *ip, int nw, float *w) {
  void bitrv208neg(float *a);
  void cftf081(float *a, float *w);

  if (n > 8) {
    cftf081(a, w);
    bitrv208neg(a);
  }
}

void bitrv208(float *a) {
  float x1r, x1i, x3r, x3i, x4r, x4i, x6r, x6i;

  x1r = a[2];
  x1i = a[3];
  x3r = a[6];
  x3i = a[7];
  x4r = a[8];
  x4i = a[9];
  x6r = a[12];
  x6i = a[13];
  a[2] = x4r;
  a[3] = x4i;
  a[6] = x6r;
  a[7] = x6i;
  a[8] = x1r;
  a[9] = x1i;
  a[12] = x3r;
  a[13] = x3i;
}

void bitrv208neg(float *a) {
  float x1r, x1i, x2r, x2i, x3r, x3i, x4r, x4i, x5r, x5i, x6r, x6i, x7r, x7i;

  x1r = a[2];
  x1i = a[3];
  x2r = a[4];
  x2i = a[5];
  x3r = a[6];
  x3i = a[7];
  x4r = a[8];
  x4i = a[9];
  x5r = a[10];
  x5i = a[11];
  x6r = a[12];
  x6i = a[13];
  x7r = a[14];
  x7i = a[15];
  a[2] = x7r;
  a[3] = x7i;
  a[4] = x3r;
  a[5] = x3i;
  a[6] = x5r;
  a[7] = x5i;
  a[8] = x1r;
  a[9] = x1i;
  a[10] = x6r;
  a[11] = x6i;
  a[12] = x2r;
  a[13] = x2i;
  a[14] = x4r;
  a[15] = x4i;
}

void cftf081(float *a, float *w) {
  float wn4r, x0r, x0i, x1r, x1i, x2r, x2i, x3r, x3i, y0r, y0i, y1r, y1i, y2r, y2i, y3r, y3i, y4r, y4i, y5r, y5i, y6r, y6i, y7r, y7i;

  wn4r = w[1];
  x0r = a[0] + a[8];
  x0i = a[1] + a[9];
  x1r = a[0] - a[8];
  x1i = a[1] - a[9];
  x2r = a[4] + a[12];
  x2i = a[5] + a[13];
  x3r = a[4] - a[12];
  x3i = a[5] - a[13];
  y0r = x0r + x2r;
  y0i = x0i + x2i;
  y2r = x0r - x2r;
  y2i = x0i - x2i;
  y1r = x1r - x3i;
  y1i = x1i + x3r;
  y3r = x1r + x3i;
  y3i = x1i - x3r;
  x0r = a[2] + a[10];
  x0i = a[3] + a[11];
  x1r = a[2] - a[10];
  x1i = a[3] - a[11];
  x2r = a[6] + a[14];
  x2i = a[7] + a[15];
  x3r = a[6] - a[14];
  x3i = a[7] - a[15];
  y4r = x0r + x2r;
  y4i = x0i + x2i;
  y6r = x0r - x2r;
  y6i = x0i - x2i;
  x0r = x1r - x3i;
  x0i = x1i + x3r;
  x2r = x1r + x3i;
  x2i = x1i - x3r;
  y5r = wn4r * (x0r - x0i);
  y5i = wn4r * (x0r + x0i);
  y7r = wn4r * (x2r - x2i);
  y7i = wn4r * (x2r + x2i);
  a[8] = y1r + y5r;
  a[9] = y1i + y5i;
  a[10] = y1r - y5r;
  a[11] = y1i - y5i;
  a[12] = y3r - y7i;
  a[13] = y3i + y7r;
  a[14] = y3r + y7i;
  a[15] = y3i - y7r;
  a[0] = y0r + y4r;
  a[1] = y0i + y4i;
  a[2] = y0r - y4r;
  a[3] = y0i - y4i;
  a[4] = y2r - y6i;
  a[5] = y2i + y6r;
  a[6] = y2r + y6i;
  a[7] = y2i - y6r;
}

void rftfsub(int n, float *a, int nc, float *c) {
  int j, k, kk, ks, m;
  float wkr, wki, xr, xi, yr, yi;

  m = n >> 1;
  ks = 2 * nc / m;
  kk = 0;
  for (j = 2; j < m; j += 2) {
    k = n - j;
    kk += ks;
    wkr = 0.5 - c[nc - kk];
    wki = c[kk];
    xr = a[j] - a[k];
    xi = a[j + 1] + a[k + 1];
    yr = wkr * xr - wki * xi;
    yi = wkr * xi + wki * xr;
    a[j] -= yr;
    a[j + 1] -= yi;
    a[k] += yr;
    a[k + 1] -= yi;
  }
}

void rftbsub(int n, float *a, int nc, float *c) {
  int j, k, kk, ks, m;
  float wkr, wki, xr, xi, yr, yi;

  m = n >> 1;
  ks = 2 * nc / m;
  kk = 0;
  for (j = 2; j < m; j += 2) {
    k = n - j;
    kk += ks;
    wkr = 0.5 - c[nc - kk];
    wki = c[kk];
    xr = a[j] - a[k];
    xi = a[j + 1] + a[k + 1];
    yr = wkr * xr + wki * xi;
    yi = wkr * xi - wki * xr;
    a[j] -= yr;
    a[j + 1] -= yi;
    a[k] += yr;
    a[k + 1] -= yi;
  }
}

void dctsub(int n, float *a, int nc, float *c) {
  int j, k, kk, ks, m;
  float wkr, wki, xr;

  m = n >> 1;
  ks = nc / n;
  kk = 0;
  for (j = 1; j < m; j++) {
    k = n - j;
    kk += ks;
    wkr = c[kk] - c[nc - kk];
    wki = c[kk] + c[nc - kk];
    xr = wki * a[j] - wkr * a[k];
    a[j] = wkr * a[j] + wki * a[k];
    a[k] = xr;
  }
  a[m] *= c[0];
}

void dstsub(int n, float *a, int nc, float *c) {
  int j, k, kk, ks, m;
  float wkr, wki, xr;

  m = n >> 1;
  ks = nc / n;
  kk = 0;
  for (j = 1; j < m; j++) {
    k = n - j;
    kk += ks;
    wkr = c[kk] - c[nc - kk];
    wki = c[kk] + c[nc - kk];
    xr = wki * a[k] - wkr * a[j];
    a[k] = wkr * a[k] + wki * a[j];
    a[j] = xr;
  }
  a[m] *= c[0];
}

}  // namespace replace
