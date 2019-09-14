#pragma once

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
#define MAX_N 2048
#define MAX_M 16384
#define debug(fmt, ...) printer.Debug(__LINE__, ":", fmt, ##__VA_ARGS__)
using namespace std;
typedef pair<int, int> pi;
typedef vector<int> vi;
typedef complex<double> comp;


struct Printer {
	template<class T>void sgl(const vector<T>& v){
		cerr<<"[";if(!v.empty()){rep(i,0,sz(v)-1){sgl(v[i]);cerr << ", ";}sgl(v.back());}cerr << "]";}
	template<class S, class T>void sgl(const pair<S, T>& v) {
		cerr<<"(";sgl(v.fst);cerr<<", ";sgl(v.second);cerr << ")";}
	template<class S>void sgl(const S& v){cerr<<v;}
	void Debug() {cerr << '\n'; }
	template<class FIRST, class... REST>void Debug(FIRST arg, REST... rest){
		sgl(arg);cerr<<" ";Debug(rest...);}
};

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
extern Printer printer;


struct hash_pair { 
	template <class T1, class T2> 
	inline size_t operator()(const pair<T1, T2>& p) const
	{ 
		auto hash1 = hash<T1>{}(p.first); 
		auto hash2 = hash<T2>{}(p.second); 
		return hash1 ^ hash2; 
	} 
}; 

class SatSolver {
	public:

	void init(int N);
	void init(int N, const vector<vi>& w);

	bool solve();
	void add_clause(const vi& vec);

	vi sat_clause();

	SatSolver();
	SatSolver(int N);
	SatSolver(int N, const vector<vi>& w);

	~SatSolver();

	private:

	int N, M; //num of var, clauses
	int MM; //original clause num

	vi *W; //clauses
	int *A; //assignment neg 0 and pos
	int *L; //level
	vector<pi> hist; //implied var and clause
	set<pi> und; //value and undicided variables
	// bitset<pi> und;

	deque<pi> unsatis; //if .sec is -1 then .fst is literal, else
	//clause to update and where it is located in the clause 

	unordered_set<pi, hash_pair> *WL; //watched literals clause and where it is located

	int *CL; //value for literal
	int *WCL; //value for clause

	int bcounter; //counter for backtrace
	int ucounter;
	int ccounter;
	double dtime;
	double cctime;

	void allocate_memory();


	void show_all();

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

	int conflict(int l);

	void wlchecker();
	
	void reduce_clause();
	
	int backtrack(int l);


};

