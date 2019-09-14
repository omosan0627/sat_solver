#ifndef SAT_SOLVER
#define SAT_SOLVER

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
typedef pair<int, int> pi;
typedef vector<int> vi;
typedef complex<double> comp;

void Debug();
template<class FIRST, class... REST>void Debug(FIRST arg, REST... rest);
template<class T>ostream& operator<<(ostream& out,const vector<T>& v);
template<class S, class T>ostream& operator<<(ostream& out,const pair<S, T>& v);

const int MAX_N = 4096;
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
};

extern Timer timer;


class SatSolver {
	public:
	int N, M; //num of var, clauses
	int MM; //original clause num

	vi W[MAX_N]; //clauses
	int A[MAX_N]; //assignment neg 0 and pos
	int L[MAX_N]; //level
	vector<pi> hist; //implied var and clause
	set<pi> und; //value and undicided variables
	// bitset<pi> und;

	deque<pi> unsatis; //if .sec is -1 then .fst is literal, else
	//clause to update and where it is located in the clause 

	struct hash_pair { 
		template <class T1, class T2> 
		inline size_t operator()(const pair<T1, T2>& p) const
		{ 
			auto hash1 = hash<T1>{}(p.first); 
			auto hash2 = hash<T2>{}(p.second); 
			return hash1 ^ hash2; 
		} 
	}; 

	unordered_set<pi, hash_pair> WL[MAX_N][2]; //watched literals clause and where it is located

	int CL[MAX_N]; //value for literal
	int WCL[MAX_N]; //value for clause

	int bcounter; //counter for backtrace
	int ucounter;
	int ccounter;
	double dtime;
	double cctime;

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


	bool unit_propagation();


	int conflict(int l) {
		ccounter++;
		double time = timer.get();
		unordered_set<int> new_equ;
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

			// if(bit[0][v]) {
			// 	bit[0][v] = 0;
			// 	lcnt -= (pl == l);
			// }
			// else if(bit[1][v]) {
			// 	bit[1][v] = 0;
			// 	lcnt -= (pl == l);
			// }
			// else continue;

			rep(i, 0, sz(W[wi])) {
				int nv = W[wi][i];

				if(abs(nv) == v || new_equ.count(nv)) continue;
				new_equ.insert(nv);

				// int at = nv < 0 ? 0 : 1;
				// if(abs(nv) == v || bit[at][abs(nv)]) continue;
				// bit[at][abs(nv)] = 1;
				
				int nl = L[abs(nv)];
				
				lcnt += (nl == l);
				if(nl < l) {
					ml = max(ml, nl);
				}
			}
		}
		vi new_eqv = vi(all(new_equ));
		// vi new_eqv;
		// rep(i, 1, N + 1) {
		// 	if(bit[0][i]) new_eqv.pb(-i);
		// 	if(bit[1][i]) new_eqv.pb(i);
		// }

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

			swap(W[M - 1][0], W[M - 1][sp.sec]);
			if(tp.sec == 0) tp.sec = sp.sec;
			swap(W[M - 1][1], W[M - 1][tp.sec]);


			rep(i, 0, 2) {
				int idx = W[M - 1][i];
				if(idx < 0) WL[abs(idx)][0].insert(pi(M - 1, i));
				else WL[abs(idx)][1].insert(pi(M - 1, i));
			}

			unsatis.pb(pi(M - 1, 1));
		}
		// debug(new_eqv);
		cctime += timer.get() - time;
		return ml;
	}

	void wlchecker() {
		int sum = 0;
		rep(i, 1, N + 1) {
			rep(j, 0, 2) {
				sum += sz(WL[i][j]);
			}
		}
		if(sum != N * 2) {
			rep(i, 1, N + 1) {
				debug(vector<pi>(all(WL[i][0])), vector<pi>(all(WL[i][1])));
			}
			debug(sum, M * 2);
		}

		rep(wi, 0, M) {
			rep(idx, 0, 2) {
				int jdx = W[wi][idx];
				if(jdx < 0) {
					// if(!WL[abs(jdx)][0].count(pi(wi, idx))) {
					// 	debug(wi, jdx, W[wi]);
					// }
					assert(WL[abs(jdx)][0].count(pi(wi, idx)));
				}
				else {
					assert(WL[abs(jdx)][1].count(pi(wi, idx)));
				}
			}
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
			rep(idx, 0, 2) {
				int jdx = W[wi][idx];
				if(jdx < 0) {
					// assert(WL[abs(jdx)][0].count(pi(wi, idx)));
					WL[abs(jdx)][0].erase(pi(wi, idx));
				}
				else {
					// assert(WL[abs(jdx)][1].count(pi(wi, idx)));
					WL[abs(jdx)][1].erase(pi(wi, idx));
				}
			}
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
			// VL[wi][0] = VL[wj][0];
			// VL[wi][1] = VL[wj][1];
			WCL[wi] = WCL[wj];
			W[wi] = W[wj];
			rep(idx, 0, 2) {
				int jdx = W[wi][idx];
				if(jdx < 0) WL[abs(jdx)][0].insert(pi(wi, idx));
				else WL[abs(jdx)][1].insert(pi(wi, idx));
			}
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
		// wlchecker();

		if(M > MM * 2) reduce_clause();
		return l + 1;
	}

	void init() {
		memset(A, 0, sizeof(A));
		memset(L, 0, sizeof(L));
		hist.clear();
		und.clear();

		unsatis.clear();

		rep(i, 0, M) 
			rep(j, 0, 2) 
				WL[i][j].clear();

		memset(CL, 0, sizeof(CL));
		memset(WCL, 0, sizeof(WCL));

		bcounter = 0;
		ucounter = 0;
		ccounter = 0;
		dtime = 0.0;
		cctime = 0.0;

		rep(i, 1, N + 1) und.insert(pi(0, i));
		int at = 0;
		rep(i, 0, M) {
			if(sz(W[i]) == 1) unsatis.pb(pi(W[i][0], -1));
			else {
				W[at] = W[i];
				// VL[at][0] = 0;
				// VL[at][1] = 1;
				rep(j, 0, 2) {
					int idx = W[at][j];
					if(idx < 0) WL[abs(idx)][0].insert(pi(at, j));
					else WL[abs(idx)][1].insert(pi(at, j));
				}
				at++;
			}
		}
		// wlchecker();
		M = at;
		MM = at;
	}


	bool sat_solver();
};



#endif
