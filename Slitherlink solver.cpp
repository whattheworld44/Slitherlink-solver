#include <cstdio>
#include <algorithm>
#include <queue>
#include <stack>
#include <map>
#include <vector>

#ifndef DIMACS
#include <cryptominisat5/cryptominisat.h>
#else
#include <fstream>
#include <vector>
#endif

namespace sat {

#ifndef DIMACS

CMSat::SATSolver solver;
std::vector<CMSat::Lit> lit_buf;

void Init(int n) { solver.new_vars(n + 1); }

void AddClause(std::vector<int> v) {
	lit_buf.clear();
	lit_buf.reserve(v.size());
	for (int x : v) lit_buf.emplace_back(abs(x), x < 0);
	solver.add_clause(lit_buf);
}

bool Solve() { return solver.solve() == CMSat::l_True; }

int GetResult(int id) {
	auto r = solver.get_model()[id];
	return r == CMSat::l_True ? 1 : r == CMSat::l_False ? -1 : 0;
}

#else

std::vector<std::vector<int>> clauses;
int n_vars;

void Init(int n) { n_vars = n; }

void AddClause(std::vector<int> v) { clauses.emplace_back(std::move(v)); }

bool Solve() {
	std::fstream fs("out.dimacs", fs.trunc | fs.out);
	fs << "p cnf " << n_vars << ' ' << clauses.size() << '\n';
	for (auto &v : clauses) {
		for (auto x : v) fs << x << ' ';
		fs << "0\n";
	}
	fs.close();
	exit(0);
}

int GetResult(int id) { return 0; }

#endif // DIMACS

}  // namespace sat
using namespace sat;
using namespace std;

void encode_intersection(int A, int B, int C, int D, int n){
	if((B%(2*n+1) > 0 && B%(2*n+1) <= n ) && C > 0 && D <= (2*n*n+n+n)){ //three road
		vector<int> cal;
		cal.clear();
		cal.push_back(-B);
		cal.push_back(-C);
		cal.push_back(-D);
		AddClause(cal);

		cal.clear();
		cal.push_back(-A);
		cal.push_back(-C);
		cal.push_back(-D);
		AddClause(cal);

		cal.clear();
		cal.push_back(-A);
		cal.push_back(-B);
		cal.push_back(-D);
		AddClause(cal);

		cal.clear();
		cal.push_back(-A);
		cal.push_back(-B);
		cal.push_back(-C);
		AddClause(cal);

		cal.clear();
		cal.push_back(A);
		cal.push_back(B);
		cal.push_back(C);
		cal.push_back(-D);
		AddClause(cal);

		cal.clear();
		cal.push_back(A);
		cal.push_back(B);
		cal.push_back(-C);
		cal.push_back(D);
		AddClause(cal);

		cal.clear();
		cal.push_back(A);
		cal.push_back(-B);
		cal.push_back(C);
		cal.push_back(D);
		AddClause(cal);

		cal.clear();
		cal.push_back(-A);
		cal.push_back(B);
		cal.push_back(C);
		cal.push_back(D);
		AddClause(cal);
	}
	else if(!(B%(2*n+1) > 0 && B%(2*n+1) <= n ) && C > 0 && D <= (2*n*n+n+n)){ // two road
		vector<int> cal;
		cal.clear();
		cal.push_back(A);
		cal.push_back(C);
		cal.push_back(-D);
		AddClause(cal);

		cal.clear();
		cal.push_back(A);
		cal.push_back(-C);
		cal.push_back(D);
		AddClause(cal);

		cal.clear();
		cal.push_back(-A);
		cal.push_back(C);
		cal.push_back(D);
		AddClause(cal);

		cal.clear();
		cal.push_back(-A);
		cal.push_back(-C);
		cal.push_back(-D);
		AddClause(cal);
	}
	else if((B%(2*n+1) > 0 && B%(2*n+1) <= n ) && C <= 0 && D <= (2*n*n+n+n)){ // two road
		vector<int> cal;
		cal.clear();
		cal.push_back(A);
		cal.push_back(B);
		cal.push_back(-D);
		AddClause(cal);

		cal.clear();
		cal.push_back(A);
		cal.push_back(-B);
		cal.push_back(D);
		AddClause(cal);

		cal.clear();
		cal.push_back(-A);
		cal.push_back(B);
		cal.push_back(D);
		AddClause(cal);

		cal.clear();
		cal.push_back(-A);
		cal.push_back(-B);
		cal.push_back(-D);
		AddClause(cal);
	}
	else if((B%(2*n+1) > 0 && B%(2*n+1) <= n ) && C > 0 && D > (2*n*n+n+n)){ // two road
		vector<int> cal;
		cal.clear();
		cal.push_back(A);
		cal.push_back(B);
		cal.push_back(-C);
		AddClause(cal);

		cal.clear();
		cal.push_back(A);
		cal.push_back(-B);
		cal.push_back(C);
		AddClause(cal);

		cal.clear();
		cal.push_back(-A);
		cal.push_back(B);
		cal.push_back(C);
		AddClause(cal);

		cal.clear();
		cal.push_back(-A);
		cal.push_back(-B);
		cal.push_back(-C);
		AddClause(cal);
	}
	else if((B%(2*n+1) > 0 && B%(2*n+1) <= n ) && C <= 0 && D > (2*n*n+n+n)){ // one road
		vector<int> cal;
		cal.clear();
		cal.push_back(A);
		cal.push_back(-B);
		AddClause(cal);
		
		cal.clear();
		cal.push_back(-A);
		cal.push_back(B);
		AddClause(cal);	
	}
	else if(!(B%(2*n+1) > 0 && B%(2*n+1) <= n ) && C > 0 && D > (2*n*n+n+n)){ // one road
		vector<int> cal;
		cal.clear();
		cal.push_back(A);
		cal.push_back(-C);
		AddClause(cal);
		
		cal.clear();
		cal.push_back(-A);
		cal.push_back(C);
		AddClause(cal);	
	}
	else if(!(B%(2*n+1) > 0 && B%(2*n+1) <= n ) && C <= 0 && D <= (2*n*n+n+n)){ // one road
		vector<int> cal;
		cal.clear();
		cal.push_back(A);
		cal.push_back(-D);
		AddClause(cal);
		
		cal.clear();
		cal.push_back(-A);
		cal.push_back(D);
		AddClause(cal);	
	}
}

void encode_board(int r, int c, int n){
	//rule 2
	for(int i=1; i<=2*r*c+r+c; i++){
		if(i%(2*n+1) <= n && i%(2*n+1) > 0){
			int LB,LC,LD;
			LB = i-1;
			LC = i-n-1;
			LD = i+n;
			encode_intersection(i, LB, LC, LD, n);
			int RB,RC,RD;
			RB = i+1;
			RC = i-n;
			RD = i+n+1;
			encode_intersection(i, RB, RC, RD, n);
		}
	}
}

void encode_number(int r, int c, int n, int number){
	int A = r*(2*n+1)+1+c;
	int B = (r+1)*(2*n+1)+1+c;
	int C = r*(2*n+1)+n+1+c;
	int D = r*(2*n+1)+n+2+c;
	if(number == 0){
		vector<int> cal;
		cal.clear();
		cal.push_back(-D);
		AddClause(cal);

		cal.clear();
		cal.push_back(-C);
		AddClause(cal);

		cal.clear();
		cal.push_back(-B);
		AddClause(cal);

		cal.clear();
		cal.push_back(-A);
		AddClause(cal);
	}
	else if(number == 1){
		vector<int> cal;
		cal.clear();
		cal.push_back(-C);
		cal.push_back(-D);
		AddClause(cal);

		cal.clear();
		cal.push_back(-B);
		cal.push_back(-D);
		AddClause(cal);
		
		cal.clear();
		cal.push_back(-B);
		cal.push_back(-C);
		AddClause(cal);

		cal.clear();
		cal.push_back(-A);
		cal.push_back(-D);
		AddClause(cal);

		cal.clear();
		cal.push_back(-A);
		cal.push_back(-C);
		AddClause(cal);

		cal.clear();
		cal.push_back(-A);
		cal.push_back(-B);
		AddClause(cal);

		cal.clear();
		cal.push_back(A);
		cal.push_back(B);
		cal.push_back(C);
		cal.push_back(D);
		AddClause(cal);
	}
	else if(number == 2){
		vector<int> cal;
		cal.clear();
		cal.push_back(A);
		cal.push_back(B);
		cal.push_back(C);
		AddClause(cal);

		cal.clear();
		cal.push_back(A);
		cal.push_back(B);
		cal.push_back(D);
		AddClause(cal);

		cal.clear();
		cal.push_back(A);
		cal.push_back(C);
		cal.push_back(D);
		AddClause(cal);

		cal.clear();
		cal.push_back(B);
		cal.push_back(C);
		cal.push_back(D);
		AddClause(cal);

		cal.clear();
		cal.push_back(-B);
		cal.push_back(-C);
		cal.push_back(-D);
		AddClause(cal);

		cal.clear();
		cal.push_back(-A);
		cal.push_back(-C);
		cal.push_back(-D);
		AddClause(cal);

		cal.clear();
		cal.push_back(-A);
		cal.push_back(-B);
		cal.push_back(-D);
		AddClause(cal);

		cal.clear();
		cal.push_back(-A);
		cal.push_back(-B);
		cal.push_back(-C);
		AddClause(cal);
	}
	else if(number == 3){
		vector<int> cal;
		cal.clear();
		cal.push_back(A);
		cal.push_back(B);
		AddClause(cal);

		cal.clear();
		cal.push_back(A);
		cal.push_back(C);
		AddClause(cal);

		cal.clear();
		cal.push_back(B);
		cal.push_back(C);
		AddClause(cal);

		cal.clear();
		cal.push_back(A);
		cal.push_back(D);
		AddClause(cal);

		cal.clear();
		cal.push_back(B);
		cal.push_back(D);
		AddClause(cal);

		cal.clear();
		cal.push_back(C);
		cal.push_back(D);
		AddClause(cal);

		cal.clear();
		cal.push_back(-A);
		cal.push_back(-B);
		cal.push_back(-C);
		cal.push_back(-D);
		AddClause(cal);
	}
	else if(number == 4){
		vector<int> cal;
		cal.clear();
		cal.push_back(A);
		AddClause(cal);

		cal.clear();
		cal.push_back(B);
		AddClause(cal);

		cal.clear();
		cal.push_back(C);
		AddClause(cal);

		cal.clear();
		cal.push_back(D);
		AddClause(cal);
	}
}

void myprint(int r, int c){
	int flag = 1;
	for(int i=1; i<=2*r*c+r+c; i++){
		if(flag == 1){
			printf("+");
			if(GetResult(i) > 0){
				printf("--");	
			}
			else if(GetResult(i) < 0){
				printf("  ");
			}
			if(i%(2*r+1) == r){
				printf("+\n");
				flag = 2;
			}
		}
		else if(flag == 2){
			if(GetResult(i) > 0){
				printf("|");
			}
			else if(GetResult(i) < 0){
				printf(" ");
			}
			if(i%(2*r+1) != 0){
				printf("  ");
			}
			else{
				printf("\n");
				flag = 1;
			}
		}
	}
	printf("\n------------divide line-------------\n");
}

queue<int> g_queue;
int isvalid(int r, int c, int n){
	vector<int> unused(2*r*c+r+c+1);
	queue<int> serve;
	int flag = 0;
	int invalid = 0;
	for(int i=1; i<=2*r*c+r+c; i++){
		if(GetResult(i) > 0){
			unused[i] = 1;
		}
		else{
			unused[i] = 0;
		}
	}

	for(int i=1; i<=2*r*c+r+c; i++){
		for(int i=1; i<=2*r*c+r+c; i++){
			if(unused[i] == 1){
				if(flag == 0){
					serve.push(i);
					flag = 1;
					break;
				}
				else{
					serve.push(i);
					invalid = 1;
					break;
				}
			}
		}
		queue<int> l_queue;
		while(!serve.empty()){
			int temp = serve.front();
			if(invalid == 0){
				g_queue.push(temp);
			}
			else{
				l_queue.push(temp);
			}
			unused[temp] = 0;
			serve.pop();
			if(temp%(2*n+1) <= n && temp%(2*n+1) > 0){ //horizontal
				int LL, LU, LD;
				LL = temp-1;
				LU = temp-n-1;
				LD = temp+n;
				int RR, RU, RD;
				RR = temp+1;
				RU = temp-n;
				RD = temp+n+1;

				if(LL%(2*n+1) > 0 && unused[LL] == 1){
					serve.push(LL);
				}
				else if(LU > 0 && unused[LU] == 1){
					serve.push(LU);
				}
				else if(LD <= (2*n*n+n+n) && unused[LD] == 1){
					serve.push(LD);
				}
				else if(RR%(2*n+1) <= n && unused[RR] == 1){
					serve.push(RR);
				}
				else if(RU > 0 && unused[RU] == 1){
					serve.push(RU);
				}
				else if(RD <= (2*n*n+n+n) && unused[RD] == 1){
					serve.push(RD);
				}
			}
			else{  									   //vertical
				int UU, UL, UR;
				UU = temp-2*n-1;
				UL = temp-n-1;
				UR = temp-n;
				int DD, DL, DR;
				DD = temp+2*n+1;
				DL = temp+n;
				DR = temp+n+1;

				if(UU > 0 && unused[UU] == 1){
					serve.push(UU);
				}
				else if(UL%(2*n+1) > 0 && unused[UL] == 1){
					serve.push(UL);
				}
				else if(UR%(2*n+1) < n+1 && unused[UR] == 1){
					serve.push(UR);
				}
				else if(DD <= (2*n*n+n+n) && unused[DD] == 1){
					serve.push(DD);
				}
				else if(DL%(2*n+1) > 0 && unused[DL] == 1){
					serve.push(DL);
				}
				else if(DR%(2*n+1) < n+1 && unused[DR] == 1){
					serve.push(DR);
				}
			}
		}
		if(invalid == 1 && l_queue.size() < g_queue.size() && !(l_queue.empty())){
			while(!g_queue.empty()){
				g_queue.pop();
			}
			while(!l_queue.empty()){
				g_queue.push(l_queue.front());
				l_queue.pop();
			}
		}
	}

	if(invalid == 1){
		return 0;
	}
	return 1;
}


int main()
{
	int r,c;
	scanf("%d%d",&r,&c);
	Init(2*r*c + r + c);

	encode_board(r ,c ,r);

	for(int i=0; i<r; i++){
		for(int j=0; j<c; j++){
			char temp;
			scanf("%c",&temp);
			if(temp == '0'){
				//printf("0");
				encode_number(i, j, r, 0);
			}
			else if(temp == '1'){
				//printf("1");
				encode_number(i, j, r, 1);
			}
			else if(temp == '2'){
				//printf("2");
				encode_number(i, j, r, 2);
			}
			else if(temp == '3'){
				//printf("3");
				encode_number(i, j, r, 3);
			}
			else if(temp == '4'){
				//printf("4");
				encode_number(i, j, r, 4);
			}
			else if(temp == '.'){
				//printf(".");
			}
			else{
				j--;
			}
		}
		//printf("\n");
	}
	int flag = 0;
	while(flag == 0){
		if(Solve() == false){
			printf("UNSATISFIABLE\n");
			return 0;
		}
		//myprint(r,c);
		if(isvalid(r, c, r) == 0){
			vector<int> cal;
			cal.clear();
			/*for(int i=1; i<=2*r*c+r+c; i++){
				cal.push_back(-1*i*GetResult(i));
			}*/
			while(!(g_queue.empty())){
				int temp = g_queue.front();
				cal.push_back(-temp);
				g_queue.pop();
			}
			AddClause(cal);
		}
		else{
			flag = 1;
		}
	}
	
	//myprint(r,c);
	for(int i=1; i<=2*r*c+r+c; i++){
		printf("%d",GetResult(i)>0?1:0);
	}
	printf("\n");

	return 0;
}
