#include <cstdio>
#include <cassert>

#include <algorithm>
#include <vector>
#include <random>

using namespace std;

using i64 = long long;
using Matrix = vector< vector<int> >;

int mod_inv(int a, int mod) {
  int b = mod, s = 1, t = 0;
  while (b) {
    int q = a / b;
    swap(a %= b, b);
    swap(s -= t * q, t);
  }
  assert(a == 1);
  return s < 0 ? s + mod : s;
}

vector<int> linear_recurrence_mod(const vector<int>& terms, const int mod) {
  const int N = terms.size() / 2;
  Matrix A(N, vector<int>(N + 1));
  for (int y = 0; y < N; ++y)
    for (int x = 0; x < N + 1; ++x)
      if ((A[y][x] = terms[x + y] % mod) < 0) A[y][x] += mod;
  int r = 0;
  for (int x = 0; x < N; ++x, ++r) {
    for (int y = x + 1; y < N; ++y) {
      while (A[y][x] > 0) {
        if (A[y][x] < A[x][x] || A[x][x] == 0) {
          for (int x2 = x; x2 < N + 1; ++x2) swap(A[x][x2], A[y][x2]);
        }
        int mq = mod - A[y][x] / A[x][x];
        for (int x2 = x; x2 < N + 1; ++x2) A[y][x2] = (A[y][x2] + i64(mq) * A[x][x2]) % mod;
      }
    }
    if (A[x][x] == 0) break;
  }
  vector<int> f(r + 1); f[0] = 1;
  for (int x = r - 1; x >= 0; --x) if (A[x][x]) {
    int g = __gcd(mod, A[x][x]); assert(A[x][r] % g == 0);
    int mc = (mod - i64(A[x][r] / g) * mod_inv(A[x][x] / g, mod / g) % mod) % mod;
    f[r - x] = mc;
    for (int y = x - 1; y >= 0; --y) A[y][r] = (A[y][r] + i64(mc) * A[y][x]) % mod;
  }
  return f;
}

void verify() {
  mt19937 mt(12345);
  for (int m = 1; m <= 100; ++m) {
    for (int mod : {m, int((1u << 31) - m)}) {
      uniform_int_distribution<int> urand(0, mod - 1);
      for (int N = 1; N <= 20; ++N) {
        uniform_int_distribution<int> urand2(0, N);
        for (int t = 0; t < 1000; ++t) {
          vector<int> terms(2 * N + 1);
          const int d = urand2(mt);
          vector<int> rec(d);
          for (int i = 0; i < d; ++i) terms[i] = urand(mt);
          for (int i = 0; i < d; ++i) rec[i] = urand(mt);
          for (int t = d; t <= 2 * N; ++t) {
            int s = 0;
            for (int i = 0; i < d; ++i) s = (s + i64(rec[i]) * terms[t - i]) % mod;
            terms[t] = s;
          }
          int expected = terms.back(); terms.pop_back();
          auto f = linear_recurrence_mod(terms, mod);
          assert(d + 1 >= int(f.size()));
          i64 ans = 0;
          for (int i = 1; i < (int) f.size(); ++i) ans += mod - i64(f[i]) * terms[2 * N - i] % mod;
          assert(ans % mod == expected);
        }
      }
      printf("passed: %d\n", mod);
    }
  }
}

void solve() {
  // SPOJ: FINDLR
  int T; assert(scanf("%d", &T) == 1);
  for (int i = 0; i < T; ++i) {
    int N, mod; assert(scanf("%d %d", &N, &mod) == 2);
    vector<int> terms(2 * N);
    for (int i = 0; i < 2 * N; ++i) assert(scanf("%d", &terms[i]) == 1);
    auto f = linear_recurrence_mod(terms, mod);
    i64 ans = 0;
    for (int i = 1; i < int(f.size()); ++i) ans += mod - i64(f[i]) * terms[2 * N - i] % mod;
    printf("%lld\n", ans % mod);
  }
}

int main() {
  verify();
  return 0;
}
