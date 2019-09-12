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
vector<pi> hist; //implied var and clause
set<int> und; //undicided variables

deque<pi> unsatis; //clause to update and where it is located in the clause
vi singlel; //single literal

set<pi> WL[MAX_N][2]; //watched literals clause and where it is located
int VL[MAX_N][2]; //watched literal "index" at clause i

void show_all() {
	int sum = 0;
	// rep(i, 1, N + 1) {
	// 	debug(i, vector<pi>(all(WL[i][0])), vector<pi>(all(WL[i][1])));
	// 	sum += sz(WL[i][0]) + sz(WL[i][1]);
	// }
	debug("sum", sum);
	// rep(i, 0, M) debug(i, VL[i][0], VL[i][1]);
	rep(i, 1, N + 2) {
		debug(i, A[i], L[i]);
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

bool update_literal(pi wp) {
	int wi = wp.fst, idx = wp.sec;
	int itarget = (VL[wi][0] != idx);
	int oidx = (itarget == 0) ? VL[wi][1] : VL[wi][0];
	// debug(idx, oidx);

	if(kai(W[wi][oidx]) > 0) return true;

	else {
		int at = -1;
		rep(i, 0, sz(W[wi])) {
			if(i == idx || i == oidx) continue;
			if(kai(W[wi][i]) >= 0) {
				at = i;
				break;
			}
		}
		if(at != -1) {
			int jdx = W[wi][idx];
			if(jdx < 0) WL[abs(jdx)][0].erase(pi(wi, idx));
			else WL[abs(jdx)][1].erase(pi(wi, idx));

			VL[wi][itarget] = at;

			jdx = W[wi][at];
			if(jdx < 0) WL[abs(jdx)][0].insert(pi(wi, at));
			else WL[abs(jdx)][1].insert(pi(wi, at));
		}
		else {
			if(kai(W[wi][oidx]) == 0) {
				int f = W[wi][oidx], s = W[wi][idx];
				hist.pb(pi(abs(f), wi));
				A[abs(f)] = f < 0 ? -1 : 1;
				L[abs(f)] = L[abs(s)];
				und.erase(abs(f));
				int at = (f < 0 ? 1 : 0);
				for(auto tp: WL[abs(f)][at]) {
					unsatis.push_back(tp);
				}
			}
			else {
				hist.pb(pi(N + 1, wi));
				L[N + 1] = -1;
				return false;
			}
		}
		return true;
	}
}


bool unit_propagation() { //redundant
	if(hist.empty()) {
		rep(i, 0, sz(singlel)) {
			int idx = W[singlel[i]][0];
			if(kai(idx) > 0) continue;
			else if(kai(idx) < 0) return false;
			else {
				A[abs(idx)] = idx < 0 ? -1 : 1;
				L[abs(idx)] = 0;
				hist.pb(pi(abs(idx), singlel[i]));
				und.erase(abs(idx));

				int at = (idx < 0 ? 1 : 0);
				for(auto wi: WL[abs(idx)][at]) {
					unsatis.push_back(wi);
				}
			}
		}
	}
	while(!unsatis.empty()) {
		pi wp = unsatis.front(); unsatis.pop_front();
		// debug("up", wp, vector<pi>(all(unsatis)));
		// show_all();
		if(!update_literal(wp)) {
			// debug(wp);
			unsatis.clear();
			return false;
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
		// if(wi == -1) {
		// 	debug(vector<pi>(all(hist)), vector<int>(all(new_equ)), lcnt);
		// 	show_all(); debug(singlel, W[singlel[0]]);
		// }
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
	// debug("new_equ", vi(all(new_equ)));
	W[M++] = vi(all(new_equ));
	if(sz(new_equ) == 1) singlel.pb(M - 1);
	else {
		pi sp = pi(-1, -1), tp = pi(-1, -1); //first and second;
		auto upd = [&](pi p) {
			if(sp < p) {
				tp = sp;
				sp = p;
			}
			else {
				tp = max(tp, p);
			}
		};
		int i = 0;
		for(auto idx : new_equ) {
			if(kai(idx) >= 0) upd(pi(N + 1, i));
			else upd(pi(L[abs(idx)], i));
			i++;
		}
		VL[M - 1][0] = sp.sec;
		VL[M - 1][1] = tp.sec;
		auto add = [&](int i) -> void{
			int idx = W[M - 1][i];
			if(idx < 0) WL[abs(idx)][0].insert(pi(M - 1, i));
			else WL[abs(idx)][1].insert(pi(M - 1, i));
		};
		add(sp.sec); add(tp.sec);
		unsatis.pb(pi(M - 1, tp.sec));
	}
	return ml;
}

int backtrack(int l) {
	while(!unit_propagation()) {
		// debug(l);
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
	// debug("backtrack", l);
	return max(l + 1, 1);
}


bool sat_solver() {
	rep(i, 0, M) {
		if(sz(W[i]) == 1) singlel.pb(i);
		else {
			VL[i][0] = 0;
			VL[i][1] = 1;
			rep(j, 0, 2) {
				int idx = W[i][j];
				if(idx < 0) WL[abs(idx)][0].insert(pi(i, j));
				else WL[abs(idx)][1].insert(pi(i, j));
			}
		}
	}
	// debug(singlel);
	// show_all();
	rep(i, 1, N + 1) und.insert(i);
	if(!unit_propagation()) return false;

	int l = 1;
	while(!und.empty()) {
		auto it = und.begin();
		int x = *it;
		und.erase(it);
		// debug("omo");
		// timer.reset();
		// while(timer.get() < 2.0) {
		// }
		// debug(x, vector<pi>(all(WL[x][0])));
		// show_all();
		A[x] = 1;
		L[x] = l;
		for(pi wp: WL[x][0]) {
			unsatis.pb(wp);
		}
		hist.push_back(pi(x, -1));
		l = backtrack(l);
		if(l == -1) return false;
	}
	return true;
}

void add(vi vec) {
	W[M++] = vec;
}

void solve() {
	N = 81 * 9; M = 0;
	rep(i, 0, 81) {
		vi vec;
		rep(j, 0, 9) {
			vec.pb(i * 9 + j + 1);
		}
		add(vec);
		rep(j, 0, 9) {
			rep(k, j + 1, 9) {
				vi vec;
				vec.pb(-(i * 9 + j + 1));
				vec.pb(-(i * 9 + k + 1));
				add(vec);
			}
		}
	}
	rep(i, 0, 9) {
		rep(k, 0, 9) {
			vi vec;
			rep(j, 0, 9) {
				vec.pb((9 * i + j) * 9 + k + 1);
			}
			add(vec);
		}
	}
	rep(j, 0, 9) {
		rep(k, 0, 9) {
			vi vec;
			rep(i, 0, 9) {
				vec.pb((9 * i + j) * 9 + k + 1);
			}
			add(vec);
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
				add(vec);
			}
		}
	}
	rep(i, 0, 9) {
		rep(j, 0, 9) {
			int b; cin >> b;
			if(b != 0) {
				vi vec;
				vec.pb((i * 9 + j) * 9 + b);
				add(vec);
			}
		}
	}
	if(!sat_solver()) {
		cout << "NO SOLUTION\n";
	}
	rep(i, 0, 9) {
		rep(j, 0, 9) {
			rep(k, 0, 9) {
				if(A[(i * 9 + j) * 9 + k + 1] == 1) {
					cout << k + 1 << " ";
					break;
				}
			}
		}
		cout << "\n";
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
	//freopen("in.txt", "wt", stdout); //for tester
	if(!freopen("in.txt", "rt", stdin)) return 1;
#endif	
	solve();
    cerr << "Time: " << 1.0 * clock() / CLOCKS_PER_SEC << " s.\n";
	return 0;
}


