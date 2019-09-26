#include <cstdio>
#include <cassert>
#include <cmath>

#include <functional>
#include <stack>

using namespace std;

using i64 = long long;
using u64 = unsigned long long;
using u128 = __uint128_t;

u128 sigma1_sum_fast(const u64 N) {
  // about O(N^{1/3} log(N))
  auto out = [N] (u64 x, u64 y) {
    return x * y > N;
  };
  auto cut = [N] (u64 x, u64, int ldx, int ldy) {
    return u128(x) * (x * ldy) >= u128(N) * ldx;
  };
  const u64 v = sqrtl(N);
  const u64 w = 4.0 * cbrtl(N);
  u64 x = v + 1;
  u64 y = v + 1;

  using T = tuple<int, int, u64, u64>;
  stack<T> stac;
  stac.emplace(1, 0, 0, 0);
  stac.emplace(0, 1, 0, 0);

  u128 ret = 0;
  while (1) {
    int ldx, ldy; u64 ls1, ls2;
    tie(ldx, ldy, ls1, ls2) = stac.top(); stac.pop();
    while (out(x + ldx, y - ldy)) {
      y -= ldy;
      ret += ls1 + ls2;
      ret += (u128(x + y) * (u64(ldx - 1) * (ldy - 1))
           +  u128(y * ldx) * (2 * x + ldx + 1) 
           +  u128(x * ldy) * (2 * y + ldy + 1)) >> 1;
      ret -= y + ldy + x + ldx;
      x += ldx;
    }
    if (y <= w) break;
    int udx = ldx, udy = ldy; u64 us1 = ls1, us2 = ls2;
    while (1) {
      tie(ldx, ldy, ls1, ls2) = stac.top();
      if (out(x + ldx, y - ldy)) break;
      udx = ldx, udy = ldy, us1 = ls1, us2 = ls2;
      stac.pop();
    }
    while (1) {
      int mdx = ldx + udx, mdy = ldy + udy;
      u64 ms1 = us1 + ls1 + u64(udx) * (udx + 1 + u64(ldy - 1) * (ldx + udx)) / 2;
      u64 ms2 = ls2 + us2 + u64(ldy) * (ldy + 1 + u64(udx - 1) * (udy + ldy)) / 2;
      if (out(x + mdx, y - mdy)) {
        stac.emplace(mdx, mdy, ms1, ms2);
        ldx = mdx, ldy = mdy, ls1 = ms1, ls2 = ms2;
      } else {
        if (cut(x + mdx, y - mdy, ldx, ldy)) break;
        udx = mdx, udy = mdy, us1 = ms1, us2 = ms2;
      }
    }
  }

  u128 s = 0;
  for (u64 i = 1; i < y; i += 2) {
    for (u64 M = N / i, k = i; k < y; M >>= 1, k <<= 1) {
      s += u128(M) * (M + 1);
      ret += k * M;
    }
  }
  ret += y * (N / y) + s / 2;
  ret -= u128(y - 1) * x * (x + 1) / 2;
  return ret - u128(N) * (N + 1) / 2;
}

u128 sigma1_sum(const u64 N) {
  u64 v = sqrtl(N);
  u128 ret = 0;
  for (u64 beg : {1, 5}) for (u64 i = beg; i <= v; i += 6) {
    for (u64 M = N / i, j = i; j <= v; j *= 3, M /= 3) {
      for (u64 L = M, k = j; k <= v; k <<= 1, L >>= 1) {
        ret += u128(L) * (L + 1 + 2 * k);
      }
    }
  }
  ret /= 2;
  return ret - u128(v) * v * (v + 1) / 2 - u128(N) * (N + 1) / 2;
}

int main() {
  for (int N = 1; N <= 10000; ++N) {
    assert(sigma1_sum(N) == sigma1_sum_fast(N));
  }
  for (u64 N = 1; N <= u64(1e18); N *= 10) {
    assert(sigma1_sum(N) == sigma1_sum_fast(N));
  }
  return 0;
}
