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

struct Timer {
	const unsigned long long int cycle_per_sec = 2800000000;
	unsigned long long int begin_cycle;

	Timer() { reset(); }
	void reset() { begin_cycle = getCycle(); }

	unsigned long long int getCycle() {
		unsigned int low, high;
		__asm__ volatile ("rdtsc" : "=a" (low), "=d" (high));
		return ((unsigned long long int)low) | ((unsigned long long int)high << 32);
	}
	 
	double get() {
		return (double)(getCycle() - begin_cycle) / cycle_per_sec;
	}
} timer;


int N, M; //num of var, clauses

vi W[MAX_N]; //clauses
int A[MAX_N]; //assignment neg 0 and pos
int L[MAX_N]; //level
int C[MAX_N]; //num of in edges
vector<pi> hist; //implied var and clause
set<int> und;

void show_all() {
	rep(i, 1, N + 2) {
		debug(i, A[i], L[i], C[i]);
	}
}

inline int kai(int idx) {
	if(A[abs(idx)] == 0) return 0;
	else if(idx < 0) {
		if(A[-idx] < 0) return 1;
		else return -1;
	}
	else {
		if(A[idx] > 0) return 1;
		else return -1;
	}
}

inline void assign_true(int idx) {
	assert(idx != 0);
	if(idx < 0) A[-idx] = -1;
	else A[idx] = 1;
}


bool unit_propagation() { //redundant
	rep(i, 0, M) {
		int neg = 0, pos = 0, zero = 0;
		int zidx = -1;
		rep(j, 0, sz(W[i])) {
			int idx = W[i][j];
			int v = kai(idx);
			if(v == 1) pos++;
			else if(v == 0) {
				zero++;
				zidx = j;
			}
			else neg++;
		}
		// debug(i, neg, pos, zero);
		if(pos == 0) {
			if(zero <= 1) {
				int to = (zidx == -1 ? N + 1 : W[i][zidx]), l = -1;
				rep(j, 0, sz(W[i])) {
					int idx = W[i][j];
					if(j == zidx) continue;

					l = max(l, L[abs(idx)]);
				}
				assign_true(to);
				L[abs(to)] = (zero == 1 ? l : -1);
				hist.push_back(pi(abs(to), i));
				und.erase(abs(to));
				if(zero == 0) return false;
				else return unit_propagation();
			}
		}
	}
	return true;
}


int conflict(int l) {
	set<int> new_equ;
	new_equ.insert(N + 1);

	int lcnt = 0, ml = -1;
	while(!hist.empty() && lcnt != 1) {
		// show_all();
		// debug("conflict", new_equ);

		pi p = hist.back(); hist.pop_back();
		int v = p.fst, wi = p.sec;
		assert(wi != -1);
		int pl = L[v];
		A[v] = 0;
		L[v] = 0;
		und.insert(v);

		if(new_equ.count(v)) {
			new_equ.erase(v);
			lcnt -= (pl == l);
		}
		else if(new_equ.count(-v)) {
			new_equ.erase(-v);
			lcnt -= (pl == l);
		}
		else continue;
		// debug(vi(all(new_equ)), ml, v, W[wi], lcnt);
		// debug(v);
		// show_all();

		rep(i, 0, sz(W[wi])) {
			int nv = W[wi][i];
			if(abs(nv) == v || new_equ.count(nv)) continue;

			new_equ.insert(nv);
			int nl = L[abs(nv)];

			lcnt += (nl == l);
			if(nl < l) {
				ml = max(ml, nl);
			}
		}
	}
	W[M++] = vi(all(new_equ));
	return ml;
}

int backtrack(int l) {
	while(!unit_propagation()) {
		if(l == -1) return -1;
		l = conflict(l);
		while(!hist.empty()) {
			pi p = hist.back();
			int v = p.fst;
			if(L[v] <= l) break;
			hist.pop_back();
			A[v] = 0;
			L[v] = 0;
			und.insert(v);
		}
	}
	return l + 1;
}


bool sat_solver() {
	if(!unit_propagation()) return false;
	rep(i, 1, N + 1) und.insert(i);

	int l = 0;
	while(!und.empty()) {
		auto it = und.begin();
		int x = *it;
		und.erase(it);
	// timer.reset();
	// while(timer.get() < 2.0) {
	// }
	// debug(x);
		// debug(x, l);
		A[x] = 1;
		L[x] = l;
		hist.push_back(pi(x, -1));
		l = backtrack(l);
		if(l == -1) return false;
	}
	return true;
}

void solve() {
	string s1, s2;
	cin >> s1 >> s2;
	cin >> N >> M;
	rep(i, 0, M) {
		int a;
		while(true) {
			cin >> a; 
			if(a == 0) break;
			W[i].pb(a);
		}
	}
	debug(sat_solver());
	rep(i, 1, N + 1) {
		debug(i, A[i]);
	}
	// rep(i, 0, 4) {
	// 	rep(j, 0, 4) {
	// 		rep(k, 0, 4) {
	// 			if(A[(i * 4 + j) * 4 + k + 1] == 1) {
	// 				cout << k + 1 << " ";
	// 				break;
	// 			}
	// 		}
	// 	}
	// 	cout << "\n";
	// }
	// rep(i, 0, M) {
	// 	debug(W[i]);
	// }
	// rep(i, 0, N + 1) {
	// 	rep(j, 0, sz(G[i])) {
	// 		debug(G[i][j].fst, i, G[i][j].sec);
	// 	}
	// }
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

