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
void Debug() {cerr << '\n'; }
template<class FIRST, class... REST>void Debug(FIRST arg, REST... rest){
	cerr<<arg<<" ";Debug(rest...);}
template<class T>ostream& operator<<(ostream& out,const vector<T>& v) {
	out<<"[";if(!v.empty()){rep(i,0,sz(v)-1)out<<v[i]<<", ";out<<v.back();}out<<"]";return out;}
template<class S, class T>ostream& operator<<(ostream& out,const pair<S, T>& v){
	out<<"("<<v.first<<", "<<v.second<<")";return out;}
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

int N;
SatSolver sat;

void solve() {
	N = 81 * 9;
	sat.init(N);
	rep(i, 0, 81) {
		vi vec;
		rep(j, 0, 9) {
			vec.pb(i * 9 + j + 1);
		}
		sat.add_clause(vec);
		rep(j, 0, 9) {
			rep(k, j + 1, 9) {
				vi vec;
				vec.pb(-(i * 9 + j + 1));
				vec.pb(-(i * 9 + k + 1));
				sat.add_clause(vec);
			}
		}
	}
	rep(i, 0, 9) {
		rep(k, 0, 9) {
			vi vec;
			rep(j, 0, 9) {
				vec.pb((9 * i + j) * 9 + k + 1);
			}
			sat.add_clause(vec);
		}
	}
	rep(j, 0, 9) {
		rep(k, 0, 9) {
			vi vec;
			rep(i, 0, 9) {
				vec.pb((9 * i + j) * 9 + k + 1);
			}
			sat.add_clause(vec);
		}
	}
	rep(i, 0, 3) {
		rep(j, 0, 3) {
			rep(k, 0, 9) {
				vi vec;
				rep(n, 0, 3) {
					rep(m, 0, 3) {
						vec.pb((i * 27 + j * 3 + n * 9 + m) * 9 + k + 1);
					}
				}
				sat.add_clause(vec);
			}
		}
	}
	rep(i, 0, 9) {
		rep(j, 0, 9) {
			int b; cin >> b;
			if(b != 0) {
				vi vec;
				vec.pb((i * 9 + j) * 9 + b);
				sat.add_clause(vec);
			}
		}
	}
	if(!sat.solve()) {
		cout << "NO SOLUTION\n";
	}
	else {
		vi ss = sat.sat_clause();
		rep(i, 0, 9) {
			rep(j, 0, 9) {
				rep(k, 0, 9) {
					if(ss[(i * 9 + j) * 9 + k] > 0) {
						cout << k + 1 << " ";
						break;
					}
				}
			}
			cout << "\n";
		}
	}
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
	ios::sync_with_stdio(false);
    cin.tie(0);
    cout << fixed;
	cout.precision(20);
    cerr << fixed;
	cerr.precision(6);
	rng.seed(rd());
	if(!freopen("numin.txt", "rt", stdin)) return 1;
	solve();
    cerr << "Time: " << 1.0 * clock() / CLOCKS_PER_SEC << " s.\n";
	return 0;
}


