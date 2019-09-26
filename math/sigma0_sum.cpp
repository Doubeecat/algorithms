#include <cstdio>
#include <cmath>
#include <cassert>

#include <functional>
#include <stack>

using namespace std;

using i64 = long long;
using u64 = unsigned long long;
using u128 = __uint128_t;

u128 sigma0_sum_fast(const u64 N) {
  auto out = [N] (u64 x, u64 y) {
    return x * y > N;
  };
  auto cut = [N] (u64 x, u64, int ldx, int ldy) {
    return u128(x) * (x * ldy) >= u128(N) * ldx;
  };
  u64 v = sqrtl(N);
  u64 w = 4.0 * cbrtl(N);
  u64 x = N / v;
  u64 y = N / x + 1;

  using T = tuple<int, int>;
  stack<T> stac;
  stac.emplace(1, 0);
  stac.emplace(1, 1);

  u128 ret = 0;
  while (1) {
    int ldx, ldy;
    tie(ldx, ldy) = stac.top(); stac.pop();
    while (out(x + ldx, y - ldy)) {
      ret += x * ldy + (u64(ldy + 1) * (ldx - 1) >> 1);
      x += ldx, y -= ldy;
    }
    if (y <= w) break;
    int udx = ldx, udy = ldy;
    while (1) {
      tie(ldx, ldy) = stac.top();
      if (out(x + ldx, y - ldy)) break;
      udx = ldx, udy = ldy;
      stac.pop();
    }
    while (1) {
      int mdx = ldx + udx, mdy = ldy + udy;
      if (out(x + mdx, y - mdy)) {
        stac.emplace(mdx, mdy);
        ldx = mdx, ldy = mdy;
      } else {
        if (cut(x + mdx, y - mdy, ldx, ldy)) break;
        udx = mdx, udy = mdy;
      }
    }
  }
  for (u64 i = 1; i < y; i += 2) {
    for (u64 M = N / i, k = i; k < y; M >>= 1, k <<= 1) ret += M;
  }
  return 2 * ret - u64(v) * v;
}

u128 sigma0_sum(const u64 N) {
  u64 v = sqrtl(N);
  u128 ret = 0;
  for (u64 beg : {1, 5}) for (u64 i = beg; i <= v; i += 6) {
    for (u64 M = N / i, j = i; j <= v; j *= 3, M /= 3) {
      for (u64 L = M, k = j; k <= v; k <<= 1, L >>= 1) {
        ret += L;
      }
    }
  }
  return 2 * ret - u64(v) * v;
}

int main() {
  for (int N = 1; N <= 10000; ++N) {
    assert(sigma0_sum(N) == sigma0_sum_fast(N));
  }
  for (u64 N = 1; N <= u64(1e18); N *= 10) {
    assert(sigma0_sum(N) == sigma0_sum_fast(N));
  }
  return 0;
}
