#include <bits/stdc++.h>
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
#define debug(fmt, ...) Debug(__LINE__, ":", fmt, ##__VA_ARGS__)
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
const int MAX_N = 500010;
const int MAX_V = 100010;
const double eps = 1e-6;
const ll mod = 1000000007;
const int inf = 1 << 30;
const ll linf = 1LL << 60;
const double PI = 3.14159265358979323846;
mt19937 rng; //use it by rng() % mod, shuffle(all(vec), rng)
///////////////////////////////////////////////////////////////////////////////////////////////////

int N, M;
vi L[MAX_N];

void add(vi vec) {
	L[M++] = vec;
}

void solve() {
	N = 4 * 4;
	rep(i, 0, 4) {
		vi vec;
		rep(j, 0, 4) {
			vec.pb(i * 4 + j + 1);
		}
		add(vec);
		rep(j, 0, 4) {
			rep(k, j + 1, 4) {
				vi vec;
				vec.pb(-(i * 4 + j + 1));
				vec.pb(-(i * 4 + k + 1));
				add(vec);
			}
		}
	}
	rep(i, 0, 1) {
		rep(k, 0, 4) {
			vi vec;
			rep(j, 0, 4) {
				vec.pb((4 * i + j) * 4 + k + 1);
			}
			add(vec);
		}
	}
	// rep(j, 0, 4) {
	// 	rep(k, 0, 4) {
	// 		vi vec;
	// 		rep(i, 0, 4) {
	// 			vec.pb((4 * i + j) * 4 + k + 1);
	// 		}
	// 		add(vec);
	// 	}
	// }
	// rep(i, 0, 2) {
	// 	rep(j, 0, 2) {
	// 		rep(k, 0, 4) {
	// 			vi vec;
	// 			rep(n, 0, 2) {
	// 				rep(m, 0, 2) {
	// 					vec.pb((i * 8 + j * 2 + n * 4 + m) * 4 + k + 1);
	// 				}
	// 			}
	// 			add(vec);
	// 		}
	// 	}
	// }
	cout << "p cnf " << N << " " << M << "\n";
	rep(i, 0, M) {
		rep(j, 0, sz(L[i])) {
			cout << L[i][j] << " ";
		}
		cout << "0\n";
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
	freopen("in.txt", "wt", stdout); //for tester
	// if(!freopen("in.txt", "rt", stdin)) return 1;
#endif	
	solve();
    cerr << "Time: " << 1.0 * clock() / CLOCKS_PER_SEC << " s.\n";
	return 0;
}

