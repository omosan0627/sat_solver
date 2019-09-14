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
int MM; //original clause num

vi W[MAX_N]; //clauses
int A[MAX_N]; //assignment neg 0 and pos
int L[MAX_N]; //level
vector<pi> hist; //implied var and clause
set<pi> und; //value and undicided variables

deque<pi> unsatis; //if .sec is -1 then .fst is literal, else
//clause to update and where it is located in the clause 

set<pi> WL[MAX_N][2]; //watched literals clause and where it is located
int VL[MAX_N][2]; //watched literal "index" at clause i
int CL[MAX_N]; //value for literal
int WCL[MAX_N]; //value for clause

int bcounter; //counter for backtrace
int ucounter;

void show_all() {
	int sum = 0;
	rep(i, 1, N + 1) {
		debug(i, vector<pi>(all(WL[i][0])), vector<pi>(all(WL[i][1])));
		sum += sz(WL[i][0]) + sz(WL[i][1]);
	}
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


bool unit_propagation() { //redundant
	ucounter++;
	while(!unsatis.empty()) {
		pi wp = unsatis.front(); unsatis.pop_front();
		if(wp.sec == -1) {
			int idx = wp.fst;
			if(kai(idx) > 0) continue;
			else if(kai(idx) < 0) return false;
			else {
				A[abs(idx)] = idx < 0 ? -1 : 1;
				L[abs(idx)] = 0;
				und.erase(pi(CL[abs(idx)], abs(idx)));

				int at = (idx < 0 ? 1 : 0);
				for(auto wi: WL[abs(idx)][at]) {
					unsatis.push_back(wi);
				}
			}
		}
		else {
			int wi = wp.fst, idx = wp.sec;
			int itarget = (VL[wi][0] != idx);
			int oidx = (itarget == 0) ? VL[wi][1] : VL[wi][0];

			if(kai(W[wi][oidx]) > 0) continue;

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
					if(jdx < 0) {
						// assert(WL[abs(jdx)][0].count(pi(wi, idx)));
						WL[abs(jdx)][0].erase(pi(wi, idx));
					}
					else {
						// assert(WL[abs(jdx)][1].count(pi(wi, idx)));
						WL[abs(jdx)][1].erase(pi(wi, idx));
					}

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
						und.erase(pi(CL[abs(f)], abs(f)));
						int at = f < 0 ? 1 : 0;
						for(auto tp: WL[abs(f)][at]) {
							unsatis.push_back(tp);
						}
					}
					else {
						hist.pb(pi(N + 1, wi));
						unsatis.clear();
						return false;
					}
				}
			}
		}
	}
	return true;
}


int conflict(int l) {
	set<int> new_equ;
	new_equ.insert(N + 1);

	int lcnt = 0, ml = 0;
	while(!hist.empty() && lcnt != 1) {
		pi p = hist.back(); hist.pop_back();
		int v = p.fst, wi = p.sec;
		assert(wi != -1);
		int pl = L[v];
		A[v] = 0;
		L[v] = 0;
		und.insert(pi(CL[v], v));
		WCL[wi]++;

		if(new_equ.count(v)) {
			new_equ.erase(v);
			lcnt -= (pl == l);
		}
		else if(new_equ.count(-v)) {
			new_equ.erase(-v);
			lcnt -= (pl == l);
		}
		else continue;

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
	vi new_eqv = vi(all(new_equ));

	if(sz(new_eqv) == 1) {
		unsatis.pb(pi(new_eqv[0], -1));
	}
	else {
		W[M++] = new_eqv;
		pi sp = pi(-1, -1), tp = pi(-1, -1); //first and second;
		auto upd = [&](pi p) {
			if(sp < p) {
				tp = sp; sp = p;
			}
			else if(tp < p){
				tp = p;
			}
		};

		rep(i, 0, sz(new_eqv)) {
			int idx = new_eqv[i];
			if(kai(idx) >= 0) upd(pi(N + 1, i));
			else upd(pi(L[abs(idx)], i));
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
	// debug(new_eqv);
	return ml;
}

void wlchecker() {
	int sum = 0;
	rep(i, 0, M) {
		rep(j, 0, 2) {
			sum += sz(WL[i][j]);
		}
	}
	if(sum != M * 2) {
		debug(sum, M * 2);
	}

	rep(wi, 0, M) {
		auto count = [&](int idx) {
			int jdx = W[wi][idx];
			if(jdx < 0) {
				if(!WL[abs(jdx)][0].count(pi(wi, idx))) {
					debug(wi, jdx, W[wi]);
				}
				assert(WL[abs(jdx)][0].count(pi(wi, idx)));
			}
			else {
				assert(WL[abs(jdx)][1].count(pi(wi, idx)));
			}
		};
		count(VL[wi][0]);
		count(VL[wi][1]);
	}
	assert(sum == M * 2);
}

void reduce_clause() {
	int addM = (MM + 1) / 2;
	assert(M >= MM + addM);

	vi vidx(M - MM);
	vi go(M, 0); //two meanings

	rep(i, 0, sz(hist)) {
		if(hist[i].sec == -1) continue;
		go[hist[i].sec] = 1;
	}
	rep(i, 0, M - MM) vidx[i] = i + MM;

	sort(all(vidx), [&](int a, int b) { 
			if(!(go[a] ^ go[b])) return WCL[a] > WCL[b];
			else if(go[a]) return true;
			else return false; });

	// vi vec;
	// rep(i, 0, M - MM) vec.pb(WCL[vidx[i]]);
	// debug(vec);
	sort(vidx.begin(), vidx.begin() + addM);

	//from now, go is where clause is located in newer
	
	rep(wi, MM, M) go[wi] = -1;

	rep(i, 0, addM) {
		go[vidx[i]] = i + MM;
	}

	rep(wi, MM, M) {
		auto erase = [&](int idx) {
			int jdx = W[wi][idx];
			if(jdx < 0) {
				if(!WL[abs(jdx)][0].count(pi(wi, idx))) {
					debug(wi, jdx);
				}
				assert(WL[abs(jdx)][0].count(pi(wi, idx)));
				WL[abs(jdx)][0].erase(pi(wi, idx));
			}
			else {
				if(!WL[abs(jdx)][1].count(pi(wi, idx))) {
					debug(wi, W[wi], MM, M);
				}
				assert(WL[abs(jdx)][1].count(pi(wi, idx)));
				WL[abs(jdx)][1].erase(pi(wi, idx));
			}
		};
		erase(VL[wi][0]);
		erase(VL[wi][1]);
	}
	// vi cwi(M, 0);
	// rep(i, 1, N + 1) {
	// 	rep(j, 0, 2) {
	// 		for(auto p: WL[i][j]) {
	// 			cwi[p.fst]++;
	// 		}
	// 	}
	// }
	// rep(i, 0, M) {
	// 	if(i < MM) assert(cwi[i] == 2);
	// 	else assert(cwi[i] == 0);
	// }

	rep(i, 0, addM) {
		int wi = i + MM;
		int wj = vidx[i];
		VL[wi][0] = VL[wj][0];
		VL[wi][1] = VL[wj][1];
		WCL[wi] = WCL[wj];
		W[wi] = W[wj];
		auto add = [&](int idx) {
			int jdx = W[wi][idx];
			if(jdx < 0) WL[abs(jdx)][0].insert(pi(wi, idx));
			else WL[abs(jdx)][1].insert(pi(wi, idx));
		};
		add(VL[wi][0]);
		add(VL[wi][1]);
	}
	rep(i, addM, M) WCL[i + MM] = 0;
	rep(i, 0, sz(hist)) {
		if(hist[i].sec == -1 || hist[i].sec < MM) continue;
		int nwi = go[hist[i].sec];
		assert(nwi != -1);
		hist[i].sec = nwi;
	}
	// debug(vector<pi>(all(hist)));
	M = MM + addM;
}

int backtrack(int l) {
	int pM = M;
	while(!unit_propagation()) {
		if(l == 0) return 0;
		l = conflict(l);
		while(!hist.empty()) {
			pi p = hist.back();
			int v = p.fst;
			if(L[v] <= l) break;
			hist.pop_back();
			A[v] = 0;
			L[v] = 0;
			und.insert(pi(CL[v], v));
		}
	}
	vi vec;
	rep(i, pM, M) {
		rep(j, 0, sz(W[i])) {
			if(und.count(pi(CL[abs(W[i][j])], abs(W[i][j])))) {
				vec.pb(abs(W[i][j]));
				und.erase(pi(CL[abs(W[i][j])], abs(W[i][j])));
			}
		}
	}
	rep(i, pM, M) {
		rep(j, 0, sz(W[i])) {
			CL[abs(W[i][j])]--;
		}
	}

	rep(i, 0, sz(vec)) {
		int v = vec[i];
		und.insert(pi(CL[v], v));
	}
	if(bcounter == 256) {
		vec.clear();
		for(auto p: und) {
			vec.pb(p.sec);
		}
		und.clear();
		rep(i, 1, N + 1) CL[i] /= 2;
		rep(i, 0, M) WCL[i] /= 2;
		rep(i, 0, sz(vec)) {
			und.insert(pi(CL[vec[i]], vec[i]));
		}
		bcounter = 0;
	}
	else bcounter++;

	assert(unsatis.empty());

	if(M > MM * 2) reduce_clause();
	// wlchecker();
	return l + 1;
}

void init() {
	MM = M;
	rep(i, 1, N + 1) und.insert(pi(0, i));
	rep(i, 0, M) {
		if(sz(W[i]) == 1) unsatis.pb(pi(W[i][0], -1));
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
}


bool sat_solver() {

	init();
	if(!unit_propagation()) return false;

	int l = 1;
	while(!und.empty()) {
		// debug("omo", timer.get());
		if(timer.get() > 2.0) {
			timer.reset();
			debug(ucounter, MM, M);
		}
		auto it = und.begin();
		int x = (*it).sec;
		und.erase(it);
		A[x] = 1;
		L[x] = l;
		for(pi wp: WL[x][0]) {
			unsatis.pb(wp);
		}
		hist.push_back(pi(x, -1));
		l = backtrack(l);
		if(!l) return false;
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
	cout << "p cnf " << N << " " << M << "\n";
	rep(i, 0, M) {
		rep(j, 0, sz(W[i])) cout << W[i][j] << " ";
		cout << "0\n";
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
	freopen("cnf.txt", "wt", stdout); //for tester
	if(!freopen("numin.txt", "rt", stdin)) return 1;
#endif	
	solve();
    cerr << "Time: " << 1.0 * clock() / CLOCKS_PER_SEC << " s.\n";
	return 0;
}


