#include <bits/stdc++.h>
#include "sat_solver.h"
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

///////////////////////////////////////////////////////////////////////////////////////////////////


Timer timer;
Printer printer;

SatSolver::SatSolver(){}
SatSolver::SatSolver(int N){init(N);}
SatSolver::SatSolver(int N, const vector<vi>& w){init(N, w);}

void SatSolver::add_clause(const vi& vec) {
	if(sz(vec) == 1) unsatis.pb(pi(vec[0], -1));
	else {
		MM++;
		W[M++] = vec;
		rep(j, 0, 2) {
			int idx = vec[j];
			if(idx < 0) WL[abs(idx)][0].insert(pi(M - 1, j));
			else WL[abs(idx)][1].insert(pi(M - 1, j));
		}
	}
}

vi SatSolver::sat_clause() {
	vi vec;
	rep(i, 1, N + 1) vec.pb(i * A[i]);
	return vec;
}

void SatSolver::init(int n) {
	N = n;
	M = 0;
	MM = 0;
	memset(A, 0, sizeof(A));
	memset(L, 0, sizeof(L));
	hist.clear();
	und.clear();

	unsatis.clear();

	rep(i, 1, N + 1) und.insert(pi(0, i));

	rep(i, 1, N + 1) {
		rep(j, 0, 2) {
			WL[i][j].clear();
		}
	}

	memset(CL, 0, sizeof(CL));
	memset(WCL, 0, sizeof(WCL));

	bcounter = 0;
	ucounter = 0;
	ccounter = 0;
	dtime = 0.0;
	cctime = 0.0;
}

void SatSolver::init(int n, const vector<vi>& w) {
	init(n);
	rep(i, 0, sz(w)) add_clause(w[i]);
}


void SatSolver::show_all() {
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


bool SatSolver::unit_propagation() { //redundant
	ucounter++;
	double time = timer.get();
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
			// int itarget = idx;
			int oidx = idx ^ 1;

			if(kai(W[wi][oidx]) > 0) continue;

			else {
				int at = -1;
				rep(i, 2, sz(W[wi])) {
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

					swap(W[wi][idx], W[wi][at]);

					jdx = W[wi][idx];
					if(jdx < 0) WL[abs(jdx)][0].insert(pi(wi, idx));
					else WL[abs(jdx)][1].insert(pi(wi, idx));
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
	dtime += timer.get() - time;
	return true;
}

int SatSolver::conflict(int l) {
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

void SatSolver::wlchecker() {
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

void SatSolver::reduce_clause() {
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

int SatSolver::backtrack(int l) {
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




bool SatSolver::solve() {
	if(!unit_propagation()) return false;

	int l = 1;
	while(!und.empty()) {
		// debug("omo", timer.get());
		if(timer.get() > 2.0) {
			timer.reset();
			debug(ccounter, dtime, cctime);
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
