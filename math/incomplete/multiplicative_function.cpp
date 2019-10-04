#include <cstdio>
#include <cassert>
#include <cmath>

#include <algorithm>
#include <vector>

#include <tuple>

using namespace std;

using i64 = long long;
using i128 = __int128_t;
using u8 = unsigned char;
using u32 = unsigned;
using u64 = unsigned long long;
using u128 = __uint128_t;

inline int isqrt(i64 n) {
  return sqrtl(n);
}

inline int icbrt(i64 n) {
  int x = cbrtl(n);
  while (i64(x) * x * x < n) ++x;
  while (i64(x) * x * x > n) --x;
  return x;
}

template <typename F>
struct InplaceFenwickTree {
  using SmallSum = typename F::SmallSum;
  using LargeSum = typename F::LargeSum;
  using Integer = typename F::Integer;

  InplaceFenwickTree(i64 N, int S, int L, vector<SmallSum>* smalls, vector<LargeSum>* larges)
      : N(N), S(S), L(L), smalls(*smalls), larges(*larges), small_sum(SmallSum(0)) {}

  void build2() {
    for (int i = (S - L) + 1; i <= S - 1; ++i) larges[i] -= larges[i + 1];
    if (L > 0) larges[S] -= smalls[S];
    for (int i = S; i > 0; --i) smalls[i] -= smalls[i - 1];
    build();
  }

  void build() {
    for (int i = 1; i <= S; ++i) {
      int parent = i + (i & -i);
      if (parent <= S) smalls[parent] += smalls[i];
    }
    small_sum = sum_lo(S);
    for (int i = 1; i <= L; ++i) {
      int parent = i + (i & -i);
      if (parent <= L) larges[S + 1 - parent] += larges[S + 1 - i];
    }
  }

  void destroy_lo() {
    for (int i = S; i > 0; --i) {
      int parent = i + (i & -i);
      if (parent <= S) smalls[parent] -= smalls[i];
    }
    for (int i = 1; i <= S; ++i) smalls[i] += smalls[i - 1];
  }

  void destroy_hi() {
    for (int i = L; i > 0; --i) {
      int parent = i + (i & -i);
      if (parent <= L) larges[S + 1 - parent] -= larges[S + 1 - i];
    }
    if (L > 0) larges[S] += smalls[S];
    for (int i = S - 1; i > S - L; --i) larges[i] += larges[i + 1];
  }

  void destroy() {
    destroy_lo();
    destroy_hi();
  }

  SmallSum sum_lo(int n) const {
    SmallSum ret = SmallSum(0);
    for (; n > 0; n &= n - 1) ret += smalls[n];
    return ret;
  }

  LargeSum sum_hi(int n) const {
    LargeSum ret = small_sum;
    for (n = S + 1 - n; n > 0; n &= n - 1) ret += larges[S + 1 - n];
    return ret;
  }

  void add_lo(int n, Integer coeff) {
    for (; n <= S; n += n & -n) smalls[n] += coeff;
    small_sum += coeff;
  }

  void add_hi(int n, Integer coeff) {
    for (n = S + 1 - n; n <= L; n += n & -n) larges[S + 1 - n] += coeff;
  }

  const i64 N;
  const int S, L;
  vector<SmallSum>& smalls;
  vector<LargeSum>& larges;
  SmallSum small_sum;
};

template <typename F>
class PrimeSummation {
  using SmallSum = typename F::SmallSum;
  using LargeSum = typename F::LargeSum;
  using Integer = typename F::Integer;

public:
  PrimeSummation(i64 N, const vector<int>& primes)
      : N(N),
        sqrt_N(isqrt(N)), cbrt_N(icbrt(N)), sixth_root_N(icbrt(sqrt_N)),
        threshold(icbrt(N)), L(N / (threshold + 1)),
        primes(primes),
        smalls(sqrt_N + 1, SmallSum(0)), larges(sqrt_N + 1, LargeSum(0)),
        fenwick(N, sqrt_N, sqrt_N - threshold, &this->smalls, &this->larges) {

    assert(N < (i64(1) << 62));
    assert(N >= 1); assert(i64(cbrt_N + 1) * i64(cbrt_N + 1) > L);
    for (int i = 1; i <= sqrt_N; ++i) smalls[i] = F::sum(i) - F::one();
    for (int i = 1; i <= sqrt_N; ++i) larges[i] = F::sum(N / i) - F::one();
    const int pi3 = upper_bound(primes.begin(), primes.end(), cbrt_N) - primes.begin();
    const int pi4 = upper_bound(primes.begin(), primes.end(), isqrt(sqrt_N)) - primes.begin();
    const int pi6 = upper_bound(primes.begin(), primes.end(), sixth_root_N) - primes.begin();
    // clock_t t0 = clock();
    calc(0, pi6);
    // clock_t t1 = clock();
    // fprintf(stderr, "S: %.4f seconds\n", double(t1 - t0) / CLOCKS_PER_SEC);
    fenwick.build2();
    calc_intermediate(pi6, pi4, [&] (int n) { return fenwick.sum_lo(n); });
    fenwick.destroy_lo();
    // clock_t t21 = clock();
    // fprintf(stderr, "M: %.4f seconds\n", double(t21 - t1) / CLOCKS_PER_SEC);
    calc_intermediate(pi4, pi3, [&] (int n) { return smalls[n]; });
    fenwick.destroy_hi();
    // clock_t t22 = clock();
    // fprintf(stderr, "M: %.4f seconds\n", double(t22 - t21) / CLOCKS_PER_SEC);
    calc(pi3, primes.size());
    // clock_t t3 = clock();
    // fprintf(stderr, "L: %.4f seconds\n", double(t3 - t22) / CLOCKS_PER_SEC);
  }

private:
  void calc(const int pi_lo, const int pi_hi) {
    for (int pi = pi_lo; pi < pi_hi; ++pi) {
      const int p = primes[pi];
      const i64 M = N / p, q = i64(p) * p;
      const int w = sqrt_N / p, v = min<i64>(sqrt_N, N / q);
      const SmallSum psum = smalls[p - 1];
      const Integer c = F()(p);
      for (int i = 1; i <= w; ++i) larges[i] -= (larges[i * p] - psum) * c;
      const int t = min(isqrt(M), v);
      for (int i = w + 1; i <= t; ++i) larges[i] -= (smalls[M / i] - psum) * c;
      for (int i = t + 1, q = M / i, r = M % i; i <= v; ++i, r -= q) {
        if (r < 0) r += i, --q;
        larges[i] -= (smalls[q] - psum) * c;
      }
      for (int j = sqrt_N / p; j >= p; --j) {
        SmallSum coeff = (smalls[j] - psum) * c;
        for (int i = j * p, e = min(sqrt_N + 1, (j + 1) * p); i < e; ++i) smalls[i] -= coeff;
      }
    }
  }

  void rec(const i64 n, const i64 M, size_t pi_beg, const Integer coeff) {
    if (n <= sqrt_N) fenwick.add_lo(n, coeff);
    else fenwick.add_hi(M, coeff);
    for (size_t pi = pi_beg; pi < primes.size(); ++pi) {
      int p = primes[pi];
      if (i128(n) * p > L) break;
      i64 nn = n, nM = M; const Integer c = F()(p);
      Integer ncoeff = coeff;
      while (i128(nn) * p <= L) rec(nn *= p, nM /= p, pi + 1, ncoeff *= c);
    }
  }

  template <typename Func>
  void calc_intermediate(const int pi_lo, const int pi_hi, Func func) {
    for (int pi = pi_lo; pi < pi_hi; ++pi) {
      const int p = primes[pi];
      const SmallSum psum = func(p - 1);
      const Integer c = F()(p);
      const int w = threshold / p;
      for (int i = 1; i <= w; ++i) larges[i] -= (larges[i * p] - psum) * c;
      const i64 M = N / p;
      const int u = min<i64>(threshold, M / p);
      const int v = min<int>(u, sqrt_N / p);
      for (int i = w + 1; i <= v; ++i) larges[i] -= (fenwick.sum_hi(i * p) - psum) * c;
      for (int i = v + 1; i <= u; ++i) larges[i] -= (func(M / i) - psum) * c;
      for (size_t pj = pi; pj < primes.size(); ++pj) {
        const int q = primes[pj];
        if (i64(p) * q > L) break;
        rec(i64(p) * q, M / q, pj, -Integer(c) * F()(q));
      }
    }
  }

private:
  const i64 N; const int sqrt_N, cbrt_N, sixth_root_N;
  const int threshold; const i64 L;
  const vector<int>& primes;

public:
  vector<SmallSum> smalls;
  vector<LargeSum> larges;

private:
  InplaceFenwickTree<F> fenwick;
};

template <typename U, typename DU>
struct FastDiv {
  static constexpr int S = sizeof(U) * 8;
  FastDiv() {}
  FastDiv(U n) : m(n) {
    s = __lg(n - 1);
    x = ((DU(1) << (s + S)) + n - 1) / n;
  }
  friend U operator / (U n, FastDiv d) {
    return (DU(n) * d.x >> d.s) >> S;
  }
  friend U operator % (U n, FastDiv d) { return n - n / d * d.m; }
  U m, x; int s;
};

template <typename F>
class MultiplicativeSummation {
  using SmallSum = typename F::SmallSum;
  using LargeSum = typename F::LargeSum;
  using Integer = typename F::Integer;

public:
  MultiplicativeSummation(i64 N,
        const vector<int>& primes,
        vector<SmallSum>* smalls,
        vector<LargeSum>* larges)
      : N(N),
        sqrt_N(isqrt(N)), cbrt_N(icbrt(N)), sixth_root_N(icbrt(sqrt_N)),
        threshold(icbrt(N)), L(N / (threshold + 1)),
        primes(primes),
        smalls(*smalls), larges(*larges),
        fenwick(N, sqrt_N, sqrt_N - threshold, &(*smalls), &(*larges)) {

    assert(N < (i64(1) << 62));
    assert(N >= 1); assert(i64(cbrt_N + 1) * i64(cbrt_N + 1) > L);
    const int pi3 = upper_bound(primes.begin(), primes.end(), cbrt_N) - primes.begin();
    const int pi6 = upper_bound(primes.begin(), primes.end(), sixth_root_N) - primes.begin();

    // clock_t t0 = clock();
    calc_larges(pi3);
    // clock_t t1 = clock();
    // fprintf(stderr, "L: %.4f seconds\n", double(t1 - t0) / CLOCKS_PER_SEC);
    fenwick.build();
    calc_intermediate(pi6, pi3);
    fenwick.destroy();
    // clock_t t2 = clock();
    // fprintf(stderr, "M: %.4f seconds\n", double(t2 - t1) / CLOCKS_PER_SEC);
    calc_smalls(pi6);
    // clock_t t3 = clock();
    // fprintf(stderr, "S: %.4f seconds\n", double(t3 - t2) / CLOCKS_PER_SEC);
  }

private:
  void calc_larges(size_t pi3) {
    for (int i = 1; i <= threshold; ++i) {
      const i64 M = N / i;
      LargeSum s = F::one() + (larges[i] - smalls[cbrt_N]);
      for (size_t pi = pi3; pi < primes.size(); ++pi) {
        int p = primes[pi];
        if (i64(p) * p > M) break;
        i64 d = i64(i) * p;
        s += F()(p, 1) * ((d <= sqrt_N ? larges[d] : smalls[M / p]) - smalls[p]);
        s += F()(p, 2);
      }
      larges[i] = s;
    }
    for (int i = threshold + 1; i <= sqrt_N - 1; ++i) larges[i] -= larges[i + 1];
    if (sqrt_N > threshold) larges[sqrt_N] -= smalls[sqrt_N];
    for (int i = sqrt_N; i > cbrt_N; --i) smalls[i] -= smalls[i - 1];
    for (int i = cbrt_N; i > 1; --i) smalls[i] = 0;
    smalls[1] = F::one();
  }

  void rec(const i64 n, const i64 M, size_t pi_beg, const Integer coeff) {
    if (n <= sqrt_N) fenwick.add_lo(n, coeff);
    else fenwick.add_hi(M, coeff);
    for (size_t pi = pi_beg; pi < primes.size(); ++pi) {
      int p = primes[pi];
      if (i128(n) * p > L) break;
      i64 nn = n, nM = M;
      for (int e = 1; i128(nn) * p <= L; ++e) {
        rec(nn *= p, nM /= p, pi + 1, coeff * F()(p, e));
      }
    }
  }

  void calc_intermediate(const int pi_lo, const int pi3) {
    pair<int, SmallSum> memo[65] = {}; // should be initialized with 0.
    for (int pi = pi3 - 1; pi >= pi_lo; --pi) {
      const int p = primes[pi]; auto fp = FastDiv<u32, u64>(p);
      for (int i = 1; i <= threshold; ++i) {
        LargeSum s = larges[i];
        i64 d = i64(i) * p; int e = 1;
        for (; d <= threshold; d *= p) s += F()(p, e++) * larges[d];
        for (; d <= sqrt_N; d *= p) s += F()(p, e++) * fenwick.sum_hi(d);
        int se = e;
        for (int M = N / d; memo[e].first != M; ++e, M = M / fp) memo[e] = {M, F()(p, e) * fenwick.sum_lo(M)};
        for (; se < e; --e) memo[e - 1].second += memo[e].second;
        larges[i] = s + memo[e].second;
      }
      i64 q = 1; i64 M = N;
      for (int e = 1; i128(q) * p <= L; ++e) rec(q *= p, M /= p, pi + 1, F()(p, e));
    }
  }

  void calc_smalls(const int pi_hi) {
    pair<int, SmallSum> memo[65] = {}; // should be initialized with 0.
    for (int pi = pi_hi - 1; pi >= 0; --pi) {
      const int p = primes[pi]; auto fp = FastDiv<u32, u64>(p);
      for (int i = 1; i <= sqrt_N; ++i) {
        LargeSum s = larges[i];
        i64 d = i64(i) * p; int e = 1;
        for (; d <= sqrt_N; d *= p) s += F()(p, e++) * larges[d];
        int se = e;
        for (int M = N / d; memo[e].first != M; ++e, M = M / fp) memo[e] = {M, F()(p, e) * smalls[M]};
        for (; se < e; --e) memo[e - 1].second += memo[e].second;
        larges[i] = s + memo[e].second;
      }
      for (int j = sqrt_N / p; j >= 1; --j) {
        const Integer coeff = smalls[j];
        i64 q = p;
        for (int e = 1; j * q <= sqrt_N; q *= p, ++e) {
          const Integer c = F()(p, e) * coeff;
          const int end = min<i64>(sqrt_N + 1, i64(j + 1) * q);
          for (int i = j * q; i < end; ++i) smalls[i] += c;
        }
      }
    }
  }

private:
  const i64 N; const int sqrt_N, cbrt_N, sixth_root_N;
  const int threshold; const i64 L;
  const vector<int>& primes;

public:
  vector<SmallSum>& smalls;
  vector<LargeSum>& larges;

private:
  InplaceFenwickTree<F> fenwick;
};

vector<int> prime_sieve(int N) {
  if (N <= 1) return vector<int>();
  const int v = isqrt(N);
  vector<bool> isp(N + 1, 1);
  for (int p = 2; p <= v; ++p) if (isp[p]) {
    for (int i = p * p; i <= N; i += p) isp[i] = false;
  }
  const int rsize = N >= 60194 ? N / (log(N) - 1.1)
                               : max(1., N / (log(N) - 1.11)) + 1;
  vector<int> primes(rsize); int ps = 0;
  for (int i = 2; i <= N; ++i) if (isp[i]) primes[ps++] = i;
  assert(ps <= rsize);
  primes.resize(ps);
  return primes;
}

struct Pow0 {
  using LargeSum = i64;
  using SmallSum = int;
  using Integer = int;
  Integer operator () (int p) const { return Integer(1); }
  static LargeSum sum(i64 N) { return LargeSum(N); }
  static Integer one() { return Integer(1); }
};

struct One {
  using LargeSum = i64;
  using SmallSum = int;
  using Integer = int;
  SmallSum operator () (int, int e) const { return 1; }
  static Integer one() { return SmallSum(1); }
};

struct Moebius {
  using LargeSum = i64;
  using SmallSum = int;
  using Integer = int;
  SmallSum operator () (int, int e) const { return (e >= 2) ? 0 : -e; }
  static Integer one() { return SmallSum(1); }
};

struct Liouville {
  using LargeSum = i64;
  using SmallSum = int;
  using Integer = int;
  SmallSum operator () (int, int e) const { return 1 - 2 * (e & 1); }
  static Integer one() { return SmallSum(1); }
};

struct DivCnt3 {
  using LargeSum = i64;
  using SmallSum = int;
  using Integer = int;
  SmallSum operator () (int, int e) const { return 1 + 3 * e; }
  static Integer one() { return SmallSum(1); }
};

void verify() {
  for (i64 N = 1; N <= 1e6; ++N) {
    const int v = isqrt(N);
    auto primes = prime_sieve(v);
    auto ps = PrimeSummation<Pow0>(N, primes);
    auto ms = MultiplicativeSummation<One>(N, primes, &ps.smalls, &ps.larges);
    assert(ms.larges[1] == One::LargeSum(N));
    if (N % 1000 == 0) printf("OK: %llu\n", N);
  }
}

i64 mertens(const i64 N) {
  const int v = isqrt(N);
  auto primes = prime_sieve(v);
  auto ps = PrimeSummation<Pow0>(N, primes);
  for (int i = 1; i <= v; ++i) ps.smalls[i] *= -1;
  for (int i = 1; i <= v; ++i) ps.larges[i] *= -1;
  auto ms = MultiplicativeSummation<Moebius>(N, primes, &ps.smalls, &ps.larges);
  return ms.larges[1];
}

i64 liouville_sum(const i64 N) {
  const int v = isqrt(N);
  auto primes = prime_sieve(v);
  auto ps = PrimeSummation<Pow0>(N, primes);
  for (int i = 1; i <= v; ++i) ps.smalls[i] *= -1;
  for (int i = 1; i <= v; ++i) ps.larges[i] *= -1;
  auto ms = MultiplicativeSummation<Liouville>(N, primes, &ps.smalls, &ps.larges);
  return ms.larges[1];
}

i64 divcnt3(const i64 N) {
  const int v = isqrt(N);
  auto primes = prime_sieve(v);
  auto ps = PrimeSummation<Pow0>(N, primes);
  for (int i = 1; i <= v; ++i) ps.smalls[i] *= 4;
  for (int i = 1; i <= v; ++i) ps.larges[i] *= 4;
  auto ms = MultiplicativeSummation<DivCnt3>(N, primes, &ps.smalls, &ps.larges);
  return ms.larges[1];
}

int main() {
  for (i64 e = 0, N = 1; e <= 14; ++e, N *= 10) {
    clock_t t0 = clock();
    auto ans1 = mertens(N);
    clock_t t1 = clock();
    printf("%2lld %18lld %.4f sec.\n", e, ans1, double(t1 - t0) / CLOCKS_PER_SEC);
    auto ans2 = liouville_sum(N);
    clock_t t2 = clock();
    printf("%2lld %18lld %.4f sec.\n", e, ans2, double(t2 - t1) / CLOCKS_PER_SEC);
    auto ans3 = divcnt3(N);
    clock_t t3 = clock();
    printf("%2lld %18lld %.4f sec.\n", e, ans3, double(t3 - t2) / CLOCKS_PER_SEC);
  }
  return 0;
}
