#include <cstdio>
#include <cassert>

#include <algorithm>
#include <vector>

using namespace std;

using i64 = long long;
using Matrix = vector< vector<int> >;
using Poly = vector<int>;

Matrix hessenberg_form_mod(const Matrix& mat, const int mod) {
  const int N = mat.size();
  Matrix H(mat);
  for (int y = 0; y < N; ++y) for (int x = 0; x < N; ++x) if ((H[y][x] %= mod) < 0) H[y][x] += mod;
  for (int x = 0; x < N - 1; ++x) {
    for (int y = x + 2; y < N; ++y) {
      while (H[y][x] > 0) {
        if (H[y][x] < H[x + 1][x] || H[x + 1][x] == 0) {
          for (int x2 = x; x2 < N; ++x2) swap(H[x + 1][x2], H[y][x2]);
          for (int y2 = 0; y2 < N; ++y2) swap(H[y2][x + 1], H[y2][y]);
        }
        int q = H[y][x] / H[x + 1][x], mq = mod - q;
        for (int x2 = x; x2 < N; ++x2) H[y][x2] = (H[y][x2] + i64(mq) * H[x + 1][x2]) % mod;
        for (int y2 = 0; y2 < N; ++y2) H[y2][x + 1] = (H[y2][x + 1] + i64(q) * H[y2][y]) % mod;
      }
    }
  }
  return H;
}

vector<int> characteristic_polynomial_mod(const Matrix& mat, const int mod) {
  const int N = mat.size();
  const auto H = hessenberg_form_mod(mat, mod);
  vector<Poly> polys(N + 1);
  Poly f(N + 1, 0); f[0] = 1 % mod;
  polys[0] = Poly(f.begin(), f.begin() + 1);
  for (int i = 0; i < N; ++i) {
    if (H[i][i]) {
      int mc = mod - H[i][i];
      for (int k = i + 1; k > 0; --k) f[k] = (f[k] + i64(mc) * f[k - 1]) % mod;
    }
    for (int j = 0, t = 1; j < i; ++j) {
      int d = i - j - 1;
      t = i64(t) * H[d + 1][d] % mod;
      if (t == 0) break;
      int mc = mod - i64(H[d][i]) * t % mod;
      if (mc == mod) continue;
      const auto& g = polys[d];
      for (int k = j + 2; k <= i + 1; ++k) f[k] = (f[k] + i64(mc) * g[k - (j + 2)]) % mod;
    }
    polys[i + 1] = Poly(f.begin(), f.begin() + i + 2);
  }
  return f;
}

int main() {
  const int N = 45;
  Matrix mat(N, vector<int>(N));
  for (int i = 0; i < N; ++i) {
    for (int j = 0; j < N; ++j) {
      mat[i][j] = (i ^ j) + i + j * j;
    }
  }
  const auto f = vector<i64>({
    1, -30360, -60655660, -32910834048, -6891631652864,
    -607026836799488, -21771649648951296, -253220688972742656, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0
  });
  for (int m = 2; m <= 1000; ++m) {
    for (int mod : {m, (1 << 31) - m}) {
      auto g = characteristic_polynomial_mod(mat, mod);
      for (int i = 0; i <= N; ++i) {
        assert((g[i] - f[i] % mod) % mod == 0);
      }
    }
  }
  return 0;
}
