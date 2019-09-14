#include <bits/stdc++.h>
#include "sat_solver.h"
#define ADD(a, b) a = (a + ll(b)) % mod
#define MUL(a, b) a = (a * ll(b)) % mod
#define MAX(a, b) a = max(a, b)
#define MIN(a, b) a = min(a, b)
#define rep(i, a, b) for(int i = int(a); i < int(b); i++)
#define rer(i, a, b) for(int i = int(a) - 1; i >= int(b); i--)
#define all(a) (a).begin(), (a).end()
#define sz(v) (int)(v).size()
#define pb push_back
#define sec second
#define fst first
using namespace std;
typedef long long ll;
typedef unsigned long long ull;
typedef pair<int, int> pi;
typedef pair<ll, ll> pl;
typedef pair<int, pi> ppi;
typedef vector<int> vi;
typedef vector<ll> vl;
typedef vector<vl> mat;
typedef complex<double> comp;
const int MAX_V = 100010;
const double eps = 1e-6;
const ll mod = 1000000007;
const int inf = 1 << 30;
const ll linf = 1LL << 60;
const double PI = 3.14159265358979323846;
mt19937 rng; //use it by rng() % mod, shuffle(all(vec), rng)
///////////////////////////////////////////////////////////////////////////////////////////////////


struct xorshift {
	unsigned int x, y, z, w;
	unsigned int t;
	xorshift() {
		x = rng(); y = rng(); z = rng(); w = rng();
		t = 0;
	}
	int rand() {
		t = x ^ (x << 11);
        x = y;
        y = z;
        z = w;
        w = (w ^ (w >> 19)) ^ (t ^ (t >> 8));
        return w & 0x7fffffff;
	}
	double drand() {
		return (double) rand() / 0x7fffffff;
	}
} gen;

SatSolver sat;

void solve() {
	// string s1, s2;
	// cin >> s1 >> s2;
	// cin >> sat.N >> sat.M;
	// rep(i, 0, sat.M) {
	// 	int a;
	// 	while(true) {
	// 		cin >> a; 
	// 		if(a == 0) break;
	// 		sat.W[i].pb(a);
	// 	}
	// }
	// cout << sat.sat_solver() << "\n";
	// rep(i, 1, sat.N + 1) {
	// 	cout << i << " " << sat.A[i] << "\n";
	// }
	// // show_all();
	// // debug(vi(CL + 1, CL + N + 1));
}

uint32_t rd() {
	uint32_t res;
#ifdef __MINGW32__
	asm volatile("rdrand %0" :"=a"(res) ::"cc");
#else
	res = std::random_device()();
#endif
	return res;
}

int main() {
#ifndef LOCAL
	ios::sync_with_stdio(false);
    cin.tie(0);
#endif
    cout << fixed;
	cout.precision(20);
    cerr << fixed;
	cerr.precision(6);
	rng.seed(rd());
#ifdef LOCAL
	//freopen("in.txt", "wt", stdout); //for tester
	if(!freopen("in.txt", "rt", stdin)) return 1;
#endif	
	solve();
    cerr << "Time: " << 1.0 * clock() / CLOCKS_PER_SEC << " s.\n";
	return 0;
}

