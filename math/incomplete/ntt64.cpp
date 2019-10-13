#include <cstdio>
#include <cassert>
#include <cmath>

#include <algorithm>
#include <vector>

#include <random>

using namespace std;

using i64 = long long;
using i128 = __int128_t;
using u64 = unsigned long long;
using u128 = __uint128_t;

constexpr u64 mul_inv(u64 n) {
  u64 x = n;
  for (int i = 0; i < 5; ++i) x *= u64(2) - n * x;
  return x;
}

template <u64 mod, u64 prim>
struct NTT {
  static_assert(!(mod >> 60), "mod should be < 2^{60}");
  static constexpr int lv = __builtin_ctzll(mod - 1);
  static_assert(lv >= 3, "(mod - 1) should be divisible by 8");

  static constexpr u64 modulus() {
    return mod;
  }

  struct LMod {
    static constexpr u64 r = -u128(mod) % mod;
    static constexpr u64 v = mul_inv(mod);
    constexpr LMod() : n(0) {}
    constexpr LMod(u64 n) : n(init(n)) {}
    constexpr LMod(const LMod& rhs) : n(rhs.n) {}
    constexpr u64 init(u64 n) const {
      return reduce(u128(n) * r);
    }
    constexpr u64 reduce(u128 x) const {
      return u64(x >> 64) + mod - u64((u128(u64(x) * v) * mod) >> 64);
    }
    constexpr u64 get() const {
      return reduce(n) % mod;
    }
    constexpr LMod pow(u64 e) const {
      LMod x = LMod(1);
      for (LMod b = *this; e; e >>= 1, b *= b) if (e & 1) x *= b;
      return x;
    }
    constexpr LMod inv() const {
      return pow(mod - 2);
    }
    constexpr LMod& operator *= (const LMod& rhs) {
      n = reduce(u128(n) * rhs.n);
      return *this;
    }
    constexpr LMod operator * (const LMod& rhs) const {
      return LMod(*this) *= rhs;
    }
    constexpr LMod& operator += (const LMod& rhs) {
      n += rhs.n;
      return *this;
    }
    constexpr LMod operator + (const LMod& rhs) const{
      return LMod(*this) += rhs;
    }
    constexpr LMod& operator -= (const LMod& rhs) {
      n += (mod << 2) - rhs.n;
      return *this;
    }
    constexpr LMod operator - (const LMod& rhs) const {
      return LMod(*this) -= rhs;
    }
    u64 n;
  };

  constexpr NTT() {
    // < (8 - 4 * sqrt(3)) * 2^{60} < 1.0718 * 2^{60}
    rs[lv] = LMod(prim).pow((mod - 1) >> lv);
    for (int i = lv - 1; i >= 0; --i) rs[i] = rs[i + 1] * rs[i + 1];
    irs[lv] = LMod(rs[lv]).inv();
    for (int i = lv - 1; i >= 0; --i) irs[i] = irs[i + 1] * irs[i + 1];
    itwopows[lv] = LMod(u64(1) << lv).inv();
    LMod two = LMod(2);
    for (int i = lv - 1; i >= 0; --i) itwopows[i] = itwopows[i + 1] * two;
    dw[0] = rs[3];
    for (int i = 1; i < lv - 2; ++i) dw[i] = dw[i - 1] * irs[i + 1] * rs[i + 3];
    dw[lv - 2] = dw[lv - 3] * irs[lv - 1];
    idw[0] = irs[3];
    for (int i = 1; i < lv - 2; ++i) idw[i] = idw[i - 1] * rs[i + 1] * irs[i + 3];
    idw[lv - 2] = idw[lv - 3] * rs[lv - 1];
  }

  void trans(int l, vector<LMod>& A) const {
    const size_t n = size_t(1) << l, nh = (n >> 1);
    const LMod one = rs[0], imag = rs[2];
    if (l & 1) for (size_t i = 0; i < nh; ++i) {
      LMod a = A[i], b = A[i + nh];
      A[i] = a + b; A[i + nh] = a - b; // < 2.1436 * 2^{60}, < 5.0718 * 2^{60}
    }
    for (int e = l & ~1; e >= 2; e -= 2) {
      const size_t m = size_t(1) << e, m4 = m >> 2;
      LMod w2 = one;
      for (size_t i = 0; i < n; i += m) {
        const LMod w1 = w2 * w2, w3 = w1 * w2; // < 1.0718 * 2^{60}
        // assume A[*] < 9.65 * 2^{60}
        for (size_t j = i; j < i + m4; ++j) {
          LMod a0 = A[j + m4 * 0] * one, a1 = A[j + m4 * 1] * w2; // < 1.65 * 2^{60}
          LMod a2 = A[j + m4 * 2] * w1,  a3 = A[j + m4 * 3] * w3; // < 1.65 * 2^{60}
          LMod t02p = a0 + a2, t13p = a1 + a3; // < 3.3 * 2^{60}, < 3.3 * 2^{60}
          LMod t02m = a0 - a2, t13m = (a1 - a3) * imag; // < 5.65 * 2^{60}, < 1.38 * 2^{60}
          A[j + m4 * 0] = t02p + t13p; A[j + m4 * 1] = t02p - t13p; // < 6.6 * 2^{60}, < 7.3 * 2^{60}
          A[j + m4 * 2] = t02m + t13m; A[j + m4 * 3] = t02m - t13m; // < 7.03 * 2^{60}, < 9.65 * 2^{60}
        }
        w2 *= dw[__builtin_ctzll(~(i >> e))];
      }
    }
  }

  void itrans(int l, vector<LMod>& A) const {
    const size_t n = size_t(1) << l, nh = (n >> 1);
    const LMod one = rs[0], imag = irs[2];
    for (int e = 2; e <= l; e += 2) {
      const size_t m = size_t(1) << e, m4 = m >> 2;
      LMod w2 = one;
      for (size_t i = 0; i < n; i += m) {
        const LMod w1 = w2 * w2, w3 = w1 * w2; // < 1.0718 * 2^{60}
        // assume A[*] < 1.65 * 2^{60}
        for (size_t j = i; j < i + m4; ++j) {
          LMod a0 = A[j + m4 * 0], a1 = A[j + m4 * 1];
          LMod a2 = A[j + m4 * 2], a3 = A[j + m4 * 3];
          LMod t01p = a0 + a1, t23p = a2 + a3; // 3.3 * 2^{60}, 3.3 * 2^{60}
          LMod t01m = a0 - a1, t23m = (a2 - a3) * imag; // 5.65 * 2^{60}, 1.38 * 2^{60}
          A[j + m4 * 0] = (t01p + t23p) * one; A[j + m4 * 2] = (t01p - t23p) * w1; // 1.45 * 2^{60}, 1.49 * 2^{60}
          A[j + m4 * 1] = (t01m + t23m) * w2;  A[j + m4 * 3] = (t01m - t23m) * w3; // 1.48 * 2^{60}, 1.65 * 2^{60}
        }
        w2 *= idw[__builtin_ctzll(~(i >> e))];
      }
    }
    if (l & 1) for (size_t i = 0; i < nh; ++i) {
      LMod a = A[i], b = A[i + nh];
      A[i] = a + b; A[i + nh] = a - b;  // < 3.3 * 2^{60}, 5.65 * 2^{60}
    }
  }

  vector<u64> convolve(const vector<u64>& f, const vector<u64>& g) const {
    // assume f[i], g[i] < 2^{60}
    const size_t s = f.size() + g.size() - 1;
    const int l = __lg(2 * s - 1); assert(l <= lv);
    const size_t sz = size_t(1) << l;
    vector<LMod> A(sz);
    for (size_t i = 0; i < f.size(); ++i) A[i] = LMod(f[i]); // < 1.0718 * 2^{60}
    trans(l, A); // < 9.65 * 2^{60}
    const LMod inv = itwopows[l];
    if (&f == &g) {
      for (size_t i = 0; i < sz; ++i) (A[i] *= A[i]) *= inv; // < 1.46 * 2^{60}
    } else {
      vector<LMod> B(sz);
      for (size_t i = 0; i < g.size(); ++i) B[i] = LMod(g[i]);
      trans(l, B);
      for (size_t i = 0; i < sz; ++i) (A[i] *= B[i]) *= inv; // < 1.46 * 2^{60}
    }
    itrans(l, A); // < 5.65 * 2^{60}
    vector<u64> ret(s);
    for (size_t i = 0; i < s; ++i) ret[i] = A[i].get();
    return ret;
  }

  LMod dw[lv - 1], idw[lv - 1], rs[lv + 1], irs[lv + 1], itwopows[lv + 1];
};

// constexpr auto ntt = NTT<998244353, 3>();
constexpr auto ntt1 = NTT<1151514404601200641, 19>();
constexpr auto ntt2 = NTT<1148418935771627521, 19>();

void verify() {
  mt19937 mt(12345);
  const auto& ntt = ntt1;
  const u64 mod = ntt.modulus();
  uniform_int_distribution<u64> urand(0, mod - 1);
  for (int N = 1; N <= 50; ++N) {
    for (int M = 1; M <= 50; ++M) {
      for (int t = 0; t < 100; ++t) {
        vector<u64> f(N), g(M);
        for (int i = 0; i < N; ++i) f[i] = urand(mt);
        for (int i = 0; i < M; ++i) g[i] = urand(mt);
        vector<u64> h1(N + M - 1);
        for (int i = 0; i < N; ++i) {
          for (int j = 0; j < M; ++j) {
            h1[i + j] = (h1[i + j] + u128(f[i]) * g[j]) % mod;
          }
        }
        auto h2 = ntt.convolve(f, g);
        for (int i = 0; i < N + M - 1; ++i) assert(h1[i] == h2[i]);
      }
    }
    printf("N: %d passed\n", N);
  }

  // poly mul
  for (int N = 1; N <= (1 << 26); N *= 2) {
    vector<u64> f(N), g(N);
    for (int i = 0; i < N; ++i) f[i] = 1;
    for (int i = 0; i < N; ++i) g[i] = 1;
    clock_t beg = clock();
    auto h1 = ntt1.convolve(f, g);
    auto h2 = ntt2.convolve(f, g);
    // + CRT
    clock_t end = clock();
    assert(h1[N - 1] == u64(N));
    assert(h2[N - 1] == u64(N));
    printf("%8d x %8d: %.6f sec.\n", N, N, double(end - beg) / CLOCKS_PER_SEC);
  }
}

int main() {
  verify();
  return 0;
}
