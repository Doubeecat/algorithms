#include <cstdio>
#include <cassert>

#include <algorithm>
#include <vector>
#include <stack>

#include <tuple>
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

vector<int> solve_linear_equations_mod_m(
    const Matrix& A, const vector<int>& b, const int mod, bool verify=true) {
  const int H = A.size(), W = A[0].size(); assert(int(b.size()) == H);
  Matrix mat(H, vector<int>(W + 1));
  for (int y = 0; y < H; ++y) {
    for (int x = 0; x < W; ++x) {
      if ((mat[y][x] = A[y][x] % mod) < 0) mat[y][x] += mod;
    }
    if ((mat[y][W] = b[y] % mod) < 0) mat[y][W] += mod;
  }

  // O(W^2 * (H + log(mod)))
  int rank = 0;
  for (int x = 0; x < W; ++x) {
    for (int y = rank + 1; y < H; ++y) {
      while (mat[y][x] > 0) {
        if (mat[y][x] < mat[rank][x] || mat[rank][x] == 0) {
          for (int x2 = x; x2 < W + 1; ++x2) swap(mat[y][x2], mat[rank][x2]);
        }
        int mq = mod - mat[y][x] / mat[rank][x];
        for (int x2 = x; x2 < W + 1; ++x2) mat[y][x2] = (mat[y][x2] + i64(mq) * mat[rank][x2]) % mod;
      }
    }
    if (mat[rank][x] == 0) continue;
    if (++rank == H) break;
  }
  for (int y = rank; y < H; ++y) if (mat[y][W] != 0) return vector<int>();

  // O(min(H, W)^2 * (W + log(mod)))
  vector<int> ret(W, 0);
  stack< tuple<int, int, int> > stac;
  for (int y = rank - 1, v = W - (rank - y); y >= 0; --y) {
    for (int x = v - 1; x >= 0; --x) {
      while (mat[y][x] > 0) {
        if (mat[y][x] < mat[y][v] || mat[y][v] == 0) {
          for (int y2 = 0; y2 <= y; ++y2) swap(mat[y2][x], mat[y2][v]);
          stac.emplace(x, v, 0);
        }
        int mq = mod - mat[y][x] / mat[y][v];
        for (int y2 = 0; y2 <= y; ++y2) mat[y2][x] = (mat[y2][x] + i64(mq) * mat[y2][v]) % mod;
        stac.emplace(x, v, mq);
      }
    }
    int g = __gcd(mat[y][v], mod);
    if (mat[y][W] % g != 0) return vector<int>();
    mat[y][W] /= g; mat[y][v] /= g;
    if (g == 1) {
      int c = i64(mat[y][W]) * mod_inv(mat[y][v], mod / g) % mod, mc = mod - c;
      for (int y2 = 0; y2 < y; ++y2) mat[y2][W] = (mat[y2][W] + i64(mc) * mat[y2][v]) % mod;
      ret[v--] = c;
    } else {
      int w = ret.size();
      ret.emplace_back(mat[y][W]);
      stac.emplace(v, w, 0);
      int t = 0, s = 1, b = mod / g, a = mat[y][v];
      while (b > 0) {
        int q = b / a; stac.emplace(v, w, mod - q);
        t -= s * q; b -= a * q;
        if (b == 0) break;
        swap(s, t); swap(a, b); stac.emplace(v, w, 0);
      }
      if (s < 0) s += mod;
      int mq = i64(mod - s) * mat[y][W] % mod;
      for (int y2 = 0; y2 < y; ++y2) mat[y2][W] = (mat[y2][W] + i64(mq) * mat[y2][v]) % mod;
      if (t < 0) t += mod;
      for (int y2 = 0; y2 < y; ++y2) mat[y2][v] = i64(t) * mat[y2][v] % mod;
    }
  }
  while (!stac.empty()) {
    int x0, x1, c; tie(x0, x1, c) = stac.top(); stac.pop();
    if (c == 0) swap(ret[x0], ret[x1]);
    else ret[x1] = (ret[x1] + i64(ret[x0]) * c) % mod;
  }
  ret.resize(W);
  if (verify) {
    for (int y = 0; y < H; ++y) {
      int s = 0;
      for (int x = 0; x < W; ++x) s = (s + i64(A[y][x]) * ret[x]) % mod;
      assert((s - b[y] % mod) % mod == 0);
    }
  }
  return ret;
}

void verify() {
  assert(solve_linear_equations_mod_m({{105, 70, 42, 30}}, {1}, 210).size() > 0);
  assert(solve_linear_equations_mod_m({{105, 70, 42}}, {1}, 210).size() == 0);
  {
    const int N = 512;
    Matrix A(N, vector<int>(N));
    vector<int> b(N);
    for (int i = 0; i < N; ++i) {
      for (int j = i; j < N; ++j) A[i][j] = A[j][i] = 2 * i + 2;
      b[i] = 2 * (i + 1) * (i + 1);
    }
    assert(solve_linear_equations_mod_m(A, b, 1 << 30).size() > 0);
  }

  mt19937 mt(12345);
  for (int m = 1; m <= 100; ++m) {
    for (int mod : {m, m * m, m * m * m, int((1ll << 31) - m)}) {
      uniform_int_distribution<int> urand(0, mod - 1);
      auto random_matrix = [&] (const int H, const int W) {
        Matrix A(H, vector<int>(W));
        for (int y = 0; y < H; ++y) for (int x = 0; x < W; ++x) A[y][x] = urand(mt);
        return A;
      };
      auto random_vector = [&] (const int n) {
        vector<int> v(n);
        for (int x = 0; x < n; ++x) v[x] = urand(mt);
        return v;
      };
      auto mul = [&] (const Matrix& A, const vector<int>& v) {
        const int H = A.size(), W = A[0].size();
        vector<int> b(H);
        for (int y = 0; y < H; ++y) {
          int s = 0;
          for (int x = 0; x < W; ++x) s = (s + i64(A[y][x]) * v[x]) % mod;
          b[y] = s;
        }
        return b;
      };
      for (int H = 1; H <= 10; ++H) {
        for (int W = 1; W <= 10; ++W) {
          for (int t = 0; t < 10000; ++t) {
            const auto A = random_matrix(H, W);
            const auto x = random_vector(W);
            auto b = mul(A, x);
            auto y = solve_linear_equations_mod_m(A, b, mod);
            assert(y.size() > 0);
          }
        }
      }
      printf("passed: %d\n", mod);
    }
  }
}

int main() {
  verify();
  return 0;
}
