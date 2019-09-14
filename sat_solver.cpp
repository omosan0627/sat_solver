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

void Debug() {cerr << '\n'; }
template<class FIRST, class... REST>void Debug(FIRST arg, REST... rest){
	cerr<<arg<<" ";Debug(rest...);}
template<class T>ostream& operator<<(ostream& out,const vector<T>& v) {
	out<<"[";if(!v.empty()){rep(i,0,sz(v)-1)out<<v[i]<<", ";out<<v.back();}out<<"]";return out;}
template<class S, class T>ostream& operator<<(ostream& out,const pair<S, T>& v){
	out<<"("<<v.first<<", "<<v.second<<")";return out;}

Timer timer;

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

bool SatSolver::sat_solver() {

		init();
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
