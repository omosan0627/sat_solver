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


int N, M; //num of var, clouses
vector<pi> G[MAX_N]; //to and clouse

vi W[MAX_N]; //clouses
int A[MAX_N]; //assignment neg 0 and pos
int L[MAX_N]; //level
int C[MAX_N]; //num of in edges

void show_all() {
	rep(i, 1, N + 2) {
		debug(i, A[i], L[i], C[i], G[i]);
	}
}

void add_edge(int from, int to, int c) {
	G[to].pb(pi(from, c));
	C[from]++;
}

void delete_edge(int v) {
	A[v] = 0;
	L[v] = 0;
	rep(i, 0, sz(G[v])) {
		C[G[v][i].fst]--;
	}
	G[v].clear();
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

bool unit_propagation() {
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

					add_edge(abs(idx), abs(to), i);
					l = max(l, L[abs(idx)]);
				}
				assign_true(to);
				L[abs(to)] = l;
				if(zero == 0) return false;
				else return unit_propagation();
			}
		}
	}
	return true;
}

void backtrack(int l) {
	rep(i, 1, N + 2) {
		if(L[i] <= l) continue;
		delete_edge(i);
	}
}

int conflict(int l) {
	deque<int> que;
	rep(i, 1, N + 1) {
		if(C[i] == 0 && L[i] == l) {
			que.push_back(i);
		}
	}
	while(!que.empty()) {
		int v = que.front(); que.pop_front();
		rep(i, 0, sz(G[v])) {
			int n = G[v][i].fst;
			if(C[n] == 1 && L[n] == l) que.push_back(n);
		}
		delete_edge(v);
	}

	vi new_equ;
	que.push_back(N + 1);

	while(!que.empty()) {

		// show_all();
		// debug("conflict", new_equ);
		int lcnt = 0;
		rep(i, 0, sz(new_equ)) {
			int nl = L[abs(new_equ[i])];
			if(nl == l) {
				lcnt++;
			}
		}
		if(lcnt == 1) break;

		int v = que.front(); que.pop_front();
		// debug(v);
		// show_all();

		int d = -1;
		rep(i, 0, sz(G[v])) {
			int n = G[v][i].fst;
			d = G[v][i].sec;
			if(C[n] == 1 && L[n] == l) que.push_back(n);
		}
		assert(d != -1);

		auto combine = [&](vi& v1, vi& v2, int v) {
			vi res;
			rep(i, 0, sz(v1)) {
				if(abs(v1[i]) == v) continue;
				res.pb(v1[i]);
			}
			rep(i, 0, sz(v2)) {
				if(abs(v2[i]) == v) continue;
				res.pb(v2[i]);
			}
			sort(all(res));
			res.erase(unique(all(res)), res.end());
			return res;
		};

		new_equ = combine(new_equ, W[d], v);
		delete_edge(v);
		// debug(new_equ, vi(all(que)), l);
	}
	W[M++] = new_equ;

	int ml = -1;
	rep(i, 0, sz(new_equ)) {
		int nl = L[abs(new_equ[i])];
		if(nl != l) {
			ml = max(ml, nl);
		}
	}
	return ml;
}

bool sat_solver(int l) {
	// timer.reset();
	// while(timer.get() < 2.0) {
	// }
	if(!unit_propagation()) {
		// show_all();
		if(l == -1) return false;
		int nl = conflict(l);
		backtrack(nl);
		return sat_solver(nl);
	}
	l++;
	rep(i, 1, N + 1) {
		if(A[i] == 0) {
			A[i] = 1;
			L[i] = l;
			if(!unit_propagation()) {
				// timer.reset();
				// while(timer.get() < 2.0) {
				// }
				int nl = conflict(l);
				backtrack(nl);
				// debug(i, l, nl);
				// show_all();
				// debug("backtrack", nl);
				return sat_solver(nl);
			}
			l++;
		}
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
	debug(sat_solver(-1));
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

