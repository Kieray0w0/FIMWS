#include<cstdio>
#include<cstring>
#include<iostream>
#include<algorithm>
#include<unordered_map>
#include<vector>
#include<numeric>
#include<cmath>
#include<array>
#include<map>
#include<set>
#include<queue>
#include<assert.h>
#include<random>
#include<ctime>
#include<chrono>
#include <climits>
using namespace std;
mt19937 rng(std::chrono::steady_clock::now().time_since_epoch().count());
#define ll long long
#define db double
#define wtype ll
#define ge getchar 
#define pun putchar('\n')
#define pu putchar
#define puk putchar(' ')
#define pb push_back
#define hl '\n'
#define ffl fflush(stdout)
typedef vector<int> vint;
typedef vector<wtype> vwtype;
typedef array<int,2> pii;
typedef pair<int,wtype> piw;
typedef array<int,3> piii;
typedef vector<pii> vpii;
typedef vector<array<int,3>> vedge;
typedef vector<array<wtype,3>> vEdge;
typedef vector<array<int,3>> vpiii;

#define forx for(int x=0;x<n;x++)
#define fory for(int y=0;y<n;y++)

struct edge{
	wtype weight;
	int x,y;
};
bool operator < (edge a,edge b){
	//if(a.weight!=b.weight)
	return a.weight>b.weight;
	//if(a.x!=b.x)return a.x<b.x;
	//return a.y<b.y;
}

struct SSSP{
	int S;//source
	vector<vector<pii>>e;//e[u] v,eid
	vector<wtype>dist,weight;
	vint pre;
	
	void dijk(){
		priority_queue<pair<wtype,int>,vector<pair<wtype,int>>,greater<>>q;
		q.push({0,S});
		dist.assign(e.size(),LLONG_MAX);
		dist[S]=0;
		while(q.size()){
			auto [d,u]=q.top();q.pop();
			if(d>dist[u])continue;
			for(auto [v,eid]:e[u]){
				if(dist[v]>dist[u]+weight[eid]){
					dist[v]=dist[u]+weight[eid];
					pre[v]=eid;
					q.push({dist[v],v});
				}
			}
		}
	}
};

struct EWBG{// edge-weighted bipartite graph
	int nx,ny,m;
	wtype N;
	bool positive;
	vector<vector<pair<int,wtype>>>EX,EY;//[v,w]

	EWBG(){
		positive=0;N=0;nx=ny=m=0;
	}

	EWBG(int nx,int ny):nx(nx),ny(ny){
		positive=0;
		EX.clear();EX.resize(nx);
		EY.clear();EY.resize(ny);
	}

	/*EWBG(EWDCBG&G):nx(G.nx),ny(G.ny),N(G.N),m(G.m){
		positive=0;
		EX.clear();EX.resize(nx);
		EY.clear();EY.resize(ny);
		for(int x=0;x<nx;x++){
			for(auto [y,eid]:G.EX[x]){
				EX[x].pb({y,G.weight[eid]});
				EY[y].pb({x,G.weight[eid]});
			}
		}
	}*/

	void print(){
		printf("nx=%d ny=%d |V|=%d |E|=%d N=%lld\n",nx,ny,nx+ny,m,N);
	}

	void print_graph(){
		printf("print graph\n");
		print();
		for(int x=0;x<nx;x++){
			for(auto [y,w]:EX[x]){
				printf("%d %d %lld\n",x,y,w);
			}
		}
	}

	void Add(int x,int y,wtype w){
		N=max(N,abs(w));
		EX[x].pb({y,w});
		EY[y].pb({x,w});
	}

	void pre(vector<array<wtype,3>>&E){
		m=E.size();
		for(auto [x,y,w]:E){
			N=max(N,abs(w));
			Add(x,y,w);
			if(w<=0)positive=0;
		}
	}

	void EXY(){
		for(int x=0;x<nx;x++){
			for(auto [y,w]:EX[x]){
				EY[y].pb({x,w});
			}
		}
	}

	void max_del_dup(){
		//delete duplicate edges
		//find max subgraph so del min
		N=0; m=0;

		for(int x=0;x<nx;x++){
			sort(EX[x].begin(),EX[x].end(),greater<>());
			vector<piw>EXx;
			int y=-1;
			for(auto [v,w]:EX[x])
				if(v!=y){
					y=v;
					N=max(N,abs(w));
					m++;
					EXx.pb({v,w});
				}
			EX[x]=EXx;
		}

		for(int y=0;y<ny;y++){
			sort(EY[y].begin(),EY[y].end(),greater<>());
			vector<piw>EYy;
			int x=-1;
			for(auto [v,w]:EY[y])
				if(v!=x){
					x=v;
					N=max(N,abs(w));
					EYy.pb({v,w});
				}
			EY[y]=EYy;
		}
	}

	void min_del_dup(){
		//delete duplicate edges
		//find min subgraph so del max 
		N=0; m=0;

		for(int x=0;x<nx;x++){
			sort(EX[x].begin(),EX[x].end());
			vector<piw>EXx;
			int y=-1;
			for(auto [v,w]:EX[x])
				if(v!=y){
					y=v;
					N=max(N,abs(w));
					m++;
					EXx.pb({v,w});
				}
			EX[x]=EXx;
		}

		for(int y=0;y<ny;y++){
			sort(EY[y].begin(),EY[y].end());
			vector<piw>EYy;
			int x=-1;
			for(auto [v,w]:EY[y])
				if(v!=x){
					x=v;
					N=max(N,abs(w));
					EYy.pb({v,w});
				}
			EY[y]=EYy;
		}
	}

	void random_graph_p_d_max(int m_,int N_){
		//positive del_dup 
		//find max subgraph
		positive=1;
		N=N_; m=m_;
		vector<array<wtype,3>>E;
		for(int u=0;u<nx;u++){
			int v=rng()%ny;
			wtype w=rng()%N+1;
			E.pb({u,v,w});
		}
		for(int v=0;v<ny;v++){
			int u=rng()%nx;
			wtype w=rng()%N+1;
			E.pb({u,v,w});
		}
		for(int i=0;i<m-nx-ny;i++){
			int u=rng()%nx;
			int v=rng()%ny;
			wtype w=rng()%N+1;
			E.pb({u,v,w});
		}

		pre(E);
		max_del_dup();
	}

	void random_graph_d_min(int m_,int N_){
		//del_dup 
		//find min subgraph
		positive=0;
		N=N_; m=m_;
		vector<array<wtype,3>>E;
		for(int i=0;i<m;i++){
			int u=rng()%nx;
			int v=rng()%ny;
			wtype w=rng()%(N*2+1)-N;
			E.pb({u,v,w});
		}

		pre(E);
		min_del_dup();
	}
};


struct MWPM{
	int nx,ny,n;
	wtype N; 
	vector<vector<piw>>EX,EY,Ex,Ey;//[v,w]
	vint lx,ly;
	vector<piw>xy,yx;//y,w
	int sz;//match sz

	MWPM(EWBG&G):nx(G.nx),ny(G.ny),EX(G.EX),EY(G.EY),N(G.N){
		lx.clear(); lx.resize(nx);
		ly.clear(); ly.resize(ny);
		n=nx+ny;
		sz=0;
		xy.assign(nx,{-1,0});
		yx.assign(ny,{-1,0});
	}

	void print(){
		printf("nx=%d ny=%d |V|=%d N=%lld\n",nx,ny,nx+ny,N);
	}

	void print_graph(){
		printf("print MWPM graph\n");
		print();
		for(int x=0;x<nx;x++){
			for(auto [y,w]:EX[x]){
				printf("%d %d %lld\n",x,y,w);
			}
		}
	}

	wtype sign(wtype w){
		if(w<0)return -1;else return 1;
	}

	void magnify(wtype ma){
		//all w *= ma
		if(N==0)N=1;
		N*=abs(ma);printf("mag N=%lld\n",N);
		for(int x=0;x<nx;x++){
			for(auto&[v,w]:EX[x])w*=ma;
		}
		for(int y=0;y<ny;y++){
			for(auto&[v,w]:EY[y])w*=ma;
		}
		Ex=EX;Ey=EY;
	}

	//x is visited
	vector<bool> xiv,yiv;

	vEdge P;
	bool find_path(int x){
		xiv[x]=1;
		//P+=x
		for(auto [y,w]:Ex[x])
			if(!yiv[y] && lx[x]+ly[y]==w+(xy[x].first!=y)){//eligible
				yiv[y]=1;
				P.pb({x,w,y});
				if(yx[y].first==-1){
					return 1;
				}else{
					int z=yx[y].first;
					if(find_path(z))return 1;else 
						P.pop_back();
				}
			}
		return 0;
	}

	vector<vEdge>Ps; // x.w.y---x[1].w[1].y[1]
	bool AugMatch(){//O(m)
		xiv.clear(); xiv.resize(nx);
		yiv.clear(); yiv.resize(ny);
		Ps.clear();
		//for each free&&unvisited x\in X
		for(int x=0;x<nx;x++)if(!xiv[x] && xy[x].first==-1){
			if(find_path(x)){
				Ps.pb(P);
				P.clear();
			}
		}

		//aug along P\in Ps , ly[]--
		for(auto&P:Ps){
			sz++;
			for(auto [x,w,y]:P){
				xy[x]={y,w};
				yx[y]={x,w};
				ly[y]--;
			}
			//only add vertex, not del
		}

		return sz==nx;
	}

	void updmin(int&x,int y){
		if(x<0||y<x)x=y;
	}

	void Hungarian(){//O(m)
		queue<int>q;//left vertices going to be added to forest
		vint Dx,Dy;
		Dx.resize(nx);
		Dy.resize(ny);
		//q <- left free vertex
		for(int x=0;x<nx;x++)if(xy[x].first==-1)q.push(x);
		int Delta=0;
		//forest = L\cup R
		//\forall u\in forest:
		//	  label[u] = ql[u]+(Delta-D[u])*((v\in L?)1:-1)
		vector<vpii>bucket; bucket.resize(5*(nx+ny)+1); //[Delta+d] {u\in L,v\notin R}
		vector<bool>inL,inR; inL.resize(nx); inR.resize(ny);

		auto add_edge_to_bucket=[&](int xD,int x,int y)->void{
			if(xD<=Delta){
				printf("error: xD<=Delta\n");ffl;
				assert(0);
			}
			if(xD<bucket.size()){
				bucket[xD].pb({x,y});
			}
		};

		auto create_augmenting_path=[&]()->void{
			bool have_path=0;
			while(1){
				while(!q.empty()){
					int x=q.front();q.pop();
					//add x to forest: L+=x
					inL[x]=1;
					Dx[x]=Delta;
	
					//find all x..y
					for(auto [y,w]:Ex[x])if(!inR[y] && xy[x].first!=y){//y not in forest
						//try to augment x..y
						if(lx[x]+ly[y]!=w+1){//ineligible
							add_edge_to_bucket(w+(xy[x].first!=y)-lx[x]-ly[y]+Dx[x],x,y);
						}else{
							//add y to forest: R+=y
							inR[y]=1;
							Dy[y]=Delta;
							if(yx[y].first==-1){
								have_path=1;return;
							}else{
								int x_=yx[y].first;
								q.push(x_);
								//x_ can't be visited through other y
								//so inL[x_]==0
							}
						}
					}
				}

				//if(have_path)return;
																	
				//now forest can't augment
				//find d to adjust
				auto upd_Delta=[&]()->void{
					while(Delta+1<bucket.size()){
						Delta++;
						//lx[L]++ ly[R]--
						//then label[LR] not change
						//	so our forest must contain them all
						//some ineligible L\bar{R} may become eligible
						bool find_min_delta=0;
						for(auto [x,y]:bucket[Delta])if(!inR[y]){
							find_min_delta=1;
							//now x..y is eligible
	
							//add y to forest: R+=y
							inR[y]=1;
							Dy[y]=Delta;
							if(yx[y].first==-1){
								have_path=1;return;
							}else{
								int x_=yx[y].first;
								q.push(x_);
							}
						}
						if(find_min_delta)return;
					}
					printf("error: out of bucket size\n");ffl;
					assert(0);
				};
				
				upd_Delta();
				//now q has new vertices
				if(have_path)return;
			}
		};

		create_augmenting_path();
		
		for(int x=0;x<nx;x++)if(inL[x])lx[x]+=Delta-Dx[x];
		for(int y=0;y<ny;y++)if(inR[y])ly[y]-=Delta-Dy[y];
	}

	void ScaleMatch(){//O(m*sqrt(n))
		xy.assign(nx,{-1,0});
		yx.assign(ny,{-1,0});
		sz=0;
		while(!AugMatch()){//while not perfect
			Hungarian();
		}
	}

	void print_match(){
		ll ans=0;
		int i=0;
		for(int x=0;x<nx;x++){
			int y=xy[x].first;
			if(y!=-1){
				ans+=xy[x].second;
				printf("%d: (%d)--< %lld >--(%d)\n",++i,x,xy[x].second,y);
			}
		}
		printf("ans=%lld\n",ans);
	}

	void run(bool mx){//maximum weight perfect matching
		wtype ma=n+1;
		if(mx)ma=-ma;
		magnify(ma);
		int L;
		//N>=1
		L=__lg(N)+1;
		//w has L bits
		print();
		//print_graph();
		printf("L=%d\n",L);

		for(int tt=1;tt<=L;tt++){
			for(int x=0;x<nx;x++)lx[x]=lx[x]*2-1;
			for(int y=0;y<ny;y++)ly[y]=ly[y]*2-1;
			for(int x=0;x<nx;x++){
				Ex[x].clear();
				for(auto [y,w]:EX[x]){
					Ex[x].pb({y,sign(w)*(abs(w)>>(L-tt))});
					//printf("%d %d %lld\n",x,y,Ex[x].back().second);
				}
			}
			for(int y=0;y<ny;y++){
				Ey[y].clear();
				for(auto [x,w]:EY[y]){
					Ey[y].pb({x,sign(w)*(abs(w)>>(L-tt))});
				}
			}
			printf("round %d:\n",tt);
			ScaleMatch();
			print_match();
		}
		
		ll ans=0;
		int i=0;
		for(int x=0;x<nx;x++){
			int y=xy[x].first;
			if(y!=-1){
				xy[x].second/=ma;
				ans+=xy[x].second;
				printf("%d: (%d)--< %lld >--(%d)\n",++i,x,xy[x].second,y);
			}
		}
		printf("MWPM ans=%lld\n",ans);
	}
};

struct MWM{
	int nx,ny,n,N; 
	bool mx;
	vector<vector<piw>>EX,EY;//[v,w]
	vint lx,ly;
	vector<pii>xy,yx;//y,w
	int sz;//match sz
	EWBG H;

	MWM(EWBG&G):nx(G.nx),ny(G.ny),EX(G.EX),EY(G.EY),N(G.N){
		n=nx+ny;
		H=EWBG(n,n);
		for(int x=0;x<nx;x++){
			H.EX[x].pb({ny+x,0});
			for(auto [y,w]:EX[x]){
				H.EX[x].pb({y,w});
				H.EX[nx+y].pb({ny+x,w});
			}
		}
		for(int y=0;y<ny;y++)
			H.EX[nx+y].pb({y,0});
		H.EXY();

		H.N=N; H.m=2*G.m+n;

		printf("doubled G\n");
	}

	void run(){
		MWPM MOM(H);
		MOM.run(mx);
		int i=0;
		ll ans=0;
		for(int x=0;x<nx;x++){
			int y=MOM.xy[x].first;
			if(y<ny){
				ans+=MOM.xy[x].second;
				printf("%d: (%d)--< %lld >--(%d)\n",++i,x,MOM.xy[x].second,y);
			}
		}
		printf("MWM ans=%lld\n",ans);
	}
};

struct MWMM{
	int nx,ny,n;
	wtype N; 
	bool mx;
	vector<vector<piw>>EX,EY;//[v,w]
	vint lx,ly;
	vector<pii>xy,yx;//y,w
	int sz;//match sz
	EWBG H;
	wtype ans;

	MWMM(EWBG&G):nx(G.nx),ny(G.ny),EX(G.EX),EY(G.EY),N(G.N){
		n=nx+ny;
		H=EWBG(n,n);
		wtype W=2*n*N;
		for(int x=0;x<nx;x++){
			H.EX[x].pb({ny+x,-W});
			for(auto [y,w]:EX[x]){
				H.EX[x].pb({y,w});
				H.EX[nx+y].pb({ny+x,w});
			}
		}
		
		for(int y=0;y<ny;y++)
			H.EX[nx+y].pb({y,-W});
		H.EXY();

		H.N=N; H.m=2*G.m+n;

		printf("doubled G\n");
	}

	void run(){
		mx=1;
		MWPM MOM(H);
		MOM.run(mx);
		int i=0;
		ans=0;
		for(int x=0;x<nx;x++){
			int y=MOM.xy[x].first;
			if(y<ny){
				ans+=MOM.xy[x].second;
				printf("%d: (%d)--< %lld >--(%d)\n",++i,x,MOM.xy[x].second,y);
			}
		}
		printf("MWM ans=%lld\n",ans);
	}
};

struct EWDCBG{// edge-weighted degree-constrained bipartite graph
	int nx,ny,m;
	wtype N;
	bool positive;
	vector<vector<pii>>EX,EY;//[v,eid]
	vector<wtype>weight;
	vector<pii>cx,cy;//l,r

	EWDCBG(){
		positive=0;N=0;nx=ny=m=0;
	}

	EWDCBG(int nx,int ny):nx(nx),ny(ny){
		positive=0;
		EX.clear();EX.resize(nx);
		EY.clear();EY.resize(ny);
	}

	void read(){
		scanf("%d%d%d",&nx,&ny,&m);
		EX.clear();EX.resize(nx);
		EY.clear();EY.resize(ny);
		cx.clear();cx.resize(nx);
		cy.clear();cy.resize(ny);
		weight.clear();weight.pb(0);
		for(int i=1;i<=m;i++){
			int x,y;ll w;
			scanf("%d%d%lld",&x,&y,&w);
			weight.pb(w);
			N=max(N,abs(w));
			EX[x].pb({y,i});
			EY[y].pb({x,i});
		}
		for(int x=0;x<nx;x++){
			scanf("%d",&cx[x][1]);
		}
		for(int y=0;y<ny;y++){
			scanf("%d",&cy[y][1]);
		}

	}

	void print(){
		printf("nx=%d ny=%d |V|=%d |E|=%d N=%lld\n",nx,ny,nx+ny,m,N);
	}

	void print_graph(){
		printf("print graph\n");
		print();
		return;
		for(int x=0;x<nx;x++){
			for(auto [y,eid]:EX[x]){
				printf("%d %d [%d]%lld\n",x,y,eid,weight[eid]);
			}
		}
	}

	void Add(int x,int y,wtype w){
		N=max(N,abs(w));
		weight.pb(w);
		m++;
		EX[x].pb({y,m});
		EY[y].pb({x,m});
	}

	void pre(vector<array<wtype,3>>&E){
		m=0;weight.clear();weight.pb(0);
		for(auto [x,y,w]:E){
			N=max(N,abs(w));
			Add(x,y,w);
			if(w<=0)positive=0;
		}
	}

	void EXY(){
		for(int y=0;y<ny;y++)EY[y].clear();
		for(int x=0;x<nx;x++){
			//printf("deg_x[%d]=%d\n",x,(int)EX[x].size());
			for(auto [y,eid]:EX[x]){
				EY[y].pb({x,eid});
			}
		}
	}

	void del_dup(){
		//delete duplicate edges
		//find max subgraph so del min
		N=0; m=0;
		vector<wtype>weightx;weightx.pb(0);

		for(int x=0;x<nx;x++){
			sort(EX[x].begin(),EX[x].end(),[&](pii u,pii v){
				return u[0]<v[0];
			});
			vector<pii>EXx;
			int y=-1;
			for(auto [v,eid]:EX[x])
				if(v!=y){
					y=v;
					N=max(N,abs(weight[eid]));
					weightx.pb(weight[eid]);
					EXx.pb({v,++m});
				}
			EX[x]=EXx;
		}

		weight=weightx;
		EXY();
	}

	void max_del_dup(){
		//delete duplicate edges
		//find max subgraph so del min
		N=0; m=0;
		vector<wtype>weightx;weightx.pb(0);

		for(int x=0;x<nx;x++){
			sort(EX[x].begin(),EX[x].end(),[&](pii u,pii v){
				if(u[0]!=v[0]) return u[0]<v[0];
				return weight[u[1]]>weight[v[1]];
			});
			vector<pii>EXx;
			int y=-1;
			for(auto [v,eid]:EX[x])
				if(v!=y){
					y=v;
					N=max(N,abs(weight[eid]));
					weightx.pb(weight[eid]);
					EXx.pb({v,++m});
				}
			EX[x]=EXx;
		}

		weight=weightx;
		EXY();
	}

	void min_del_dup(){
		//delete duplicate edges
		//find min subgraph so del max 
		N=0; m=0;
		vector<wtype>weightx;weightx.pb(0);

		for(int x=0;x<nx;x++){
			sort(EX[x].begin(),EX[x].end(),[&](pii u,pii v){
				if(u[0]!=v[0]) return u[0]<v[0];
				return weight[u[1]]<weight[v[1]];
			});
			vector<pii>EXx;
			int y=-1;
			for(auto [v,eid]:EX[x])
				if(v!=y){
					y=v;
					N=max(N,abs(weight[eid]));
					weightx.pb(weight[eid]);
					EXx.pb({v,++m});
				}
			EX[x]=EXx;
		}

		weight=weightx;
		EXY();
	}

	void random_graph_p_d_max(int m_,int N_){
		//positive del_dup 
		//find max subgraph
		positive=1;
		N=N_; m=m_;
		vector<array<wtype,3>>E;
		for(int u=0;u<nx;u++){
			int v=rng()%ny;
			wtype w=rng()%N+1;
			E.pb({u,v,w});
		}
		for(int v=0;v<ny;v++){
			int u=rng()%nx;
			wtype w=rng()%N+1;
			E.pb({u,v,w});
		}
		int qx=nx*0.7,qy=ny*0.7,qm=m-nx-ny;
		while(qm){
			qm/=2;
			for(int i=0;i<qm;i++){
				int u=rng()%qx;
				int v=rng()%qy;
				wtype w=rng()%N+1;
				E.pb({u,v,w});
			}
			qx=max(100,(int)(qx*0.7));
			qy=max(1000,int(qy*0.7));
		}

		pre(E);
		del_dup();
		//max_del_dup();
	}

	void random_graph_d_min(int m_,int N_){
		//del_dup 
		//find min subgraph
		positive=0;
		N=N_; m=m_;
		vector<array<wtype,3>>E;
		for(int i=0;i<m;i++){
			int u=rng()%nx;
			int v=rng()%ny;
			wtype w=rng()%(N*2+1)-N;
			E.pb({u,v,w});
		}

		pre(E);
		del_dup();
	}
};

wtype maxN=1ll<<60;

struct MWPDCS{
	int nx,ny,n,m,capacitysum;
	wtype N; 
	vector<wtype>weight,w;//w[eid] 1..m 
	//original weight = weight
	//scale weight = w
	vector<bool>inD;
	vector<vector<pii>>EX,EY;//[v,eid]
	vint cx,cy;//capacity
	vint dx,dy;
	vwtype lx,ly;
	vector<piw>xy,yx;//y,w
	int sz;//match sz
	//int maxBucketSize;

	MWPDCS(EWDCBG&G):nx(G.nx),ny(G.ny),EX(G.EX),EY(G.EY),weight(G.weight),m(G.m),N(G.N){
		lx.clear(); lx.resize(nx);
		ly.clear(); ly.resize(ny);
		dx.clear(); dx.resize(nx);
		dy.clear(); dy.resize(ny);
		cx.clear(); cx.resize(nx);
		cy.clear(); cy.resize(ny);
		for(int x=0;x<nx;x++)cx[x]=G.cx[x][1];
		for(int y=0;y<ny;y++)cy[y]=G.cy[y][1];
		n=nx+ny;
		sz=0;
		xy.assign(nx,{-1,0});
		yx.assign(ny,{-1,0});
		inD.clear();inD.resize(m+1);
		capacitysum=0;
		for(auto r:cx)capacitysum+=r;
	}

	void print(){
		assert(weight.size()==m+1);
		printf("nx=%d ny=%d |V|=%d |E|=%d N=%lld capacitysum=%d\n",nx,ny,nx+ny,m,N,capacitysum);
	}

	void print_graph(){
		printf("print MWPDCS graph\n");
		print();
		return;
		for(int x=0;x<nx;x++){
			printf("%d:%d\n",x,(int)EX[x].size());
			for(auto [y,eid]:EX[x]){
				printf("%d %d [%d]=%lld\n",x,y,eid,weight[eid]);
			}
		}
		for(int x=0;x<nx;x++)printf("dx[%d] <= %d\n",x,cx[x]);
		for(int y=0;y<ny;y++)printf("%d >=dy[%d]\n",cy[y],y);
	}

	wtype sign(wtype w){
		if(w<0)return -1;else return 1;
	}

	void magnify(wtype ma){
		//all w *= ma
		if(N==0)N=1;
		if(maxN/abs(ma)<N){
			printf("error: N \n");
			assert(0);
		}
		N*=abs(ma);printf("mag N=%lld\n",N);
		for(auto&w:weight)w*=ma;
	}

	void printDiffW(){
		return;
		printf("printDiffW\n");
		for(int x=0;x<nx;x++){
			for(auto [y,eid]:EX[x]){
				printf("(%lld)%d %d(%lld) w[%d]=%lld dw=%lld <%d>\n",lx[x],x,y,ly[y],eid,w[eid],w[eid]-lx[x]-ly[y],
				int(inD[eid]));
				//assert(w[eid]-lx[x]-ly[y]>=-1);
				//assert(w[eid]-lx[x]-ly[y]<=3);
			}
		}
	}

	vint archivex,archivey;//each vertex has a pointer to its last unscanned edge
	
	vedge P;
	bool find_path(int x){//find a path begin at x
		while(1){//while not find
			//x always take a not in D edge
			while(archivex[x]<EX[x].size()&&inD[EX[x][archivex[x]][1]])archivex[x]++;
			//printf("x %d/%d\n",archivex[x],EX[x].size());
			if(archivex[x]==EX[x].size())return 0;//can't find path
			auto [y,eid]=EX[x][archivex[x]++];
			//try to find a path begin at eid
			//x..eid..y
			if(lx[x]+ly[y]==w[eid]+!inD[eid]){//eligible
				P.pb({x,+eid,y});//add
				//printf("+ %d..%d..%d(%d/%d)\n",x,eid,y,dy[y],cy[y]);
				if(dy[y]<cy[y]){//if y has deficiency
					dy[y]++;
					//printf("end dy[%d]=%d\n",y,dy[y]);
					return 1;//this path can end at y
				}else{
					while(1){
						//take an inD edge
						while(archivey[y]<EY[y].size()&&!inD[EY[y][archivey[y]][1]])archivey[y]++;
						//printf("y %d/%d\n",archivey[y],EY[y].size());
						if(archivey[y]==EY[y].size()){
							P.pop_back();
							//printf("-\n");
							break;//find no path, try to take another y
						}
						auto [x_,eid]=EY[y][archivey[y]++];
						if(lx[x_]+ly[y]==w[eid]+!inD[eid]){
							//y--eid--x_
							//printf("+ %d--%d--%d\n",y,eid,x_);
							P.pb({y,-eid,x_});//del
							if(find_path(x_)){
								return 1;
							}else{
								P.pop_back();//try to find another x_
								//printf("-\n");
							}
						}
					}
				}
			}
		}
	}

	vector<vedge>Ps; // x.w.y---x[1].w[1].y[1]
	bool more_sz;
	bool AugDCS(){//O(m)
		//find a maximal set of edge-disjoint augmenting paths
		// of eligible edges such that any vertex v is
		// an end of at most (upper_limit(v)=c*[v])-(d_D(v)=d*[v]) paths
		int qsz=sz;
		archivex.clear(); archivex.resize(nx);
		archivey.clear(); archivey.resize(ny);
		Ps.clear();
		//for each free&&unvisited x\in X
		for(int x=0;x<nx;x++){
			while(dx[x]<cx[x] && archivex[x]<EX[x].size()){
				//printf("dx[%d]=%d<cx[x]=%d %d/%d\n",x,dx[x],cx[x],
				//	archivex[x],EX[x].size());
				if(find_path(x)){
					dx[x]++;
					Ps.pb(P);
					P.clear();
				}
			}
		}

		//aug along P\in Ps , ly[]--
		for(auto&P:Ps){
			sz++;
			for(auto [x,eid,y]:P)if(eid>=0){//+eid
				xy[x]={y,eid};
				yx[y]={x,eid};
				//don't change label
				inD[eid]=1;
			}else{//-eid
				inD[-eid]=0;
			}
			//only add vertex's deg, not del
		}

		//printf("sz=%d capacitysum=%d\n",sz,capacitysum);
		//printf("sz=%d\n",sz);
		print_DCS();
		printDiffW();
		if(more_sz){ffl;assert(sz>qsz);}
		return sz==capacitysum;
	}

	void updmin(int&x,int y){
		if(x<0||y<x)x=y;
	}

	void Hungarian(){//O(m)
		queue<pair<int,bool>>q;//vertices going to be added to forest
		vint Dx,Dy;
		Dx.resize(nx);
		Dy.resize(ny);
		
		int Delta=0;
		//forest = L\cup R
		//\forall u\in forest:
		//	  label[u] = ql[u]+(Delta-D[u])*((v\in L?)1:-1)

		//bucket size is constant*n
		vector<vpii>bucket; bucket.resize(5*(nx+ny)/2); //[Delta+d] {u\in L,v\notin R}
		vector<bool>inL,inR; inL.resize(nx); inR.resize(ny);
		//q <- left free vertex
		for(int x=0;x<nx;x++)if(dx[x]<cx[x]){
			//printf("L+=%d Dx[x]=%d\n",x,Delta);
			q.push({x,0}),inL[x]=1;//Dx[x]=0;
		}
		auto add_edge_to_bucket=[&](wtype xD,int x,int y)->void{
			if(xD<=Delta){
				printf("error: xD<=Delta\n");ffl;
				assert(0);
			}
			//if(xD>=bucket.size())bucket.resize(xD+1);
			if(xD<bucket.size()){
				bucket[xD].pb({x,y});
			}
		};

		auto create_augmenting_path=[&]()->void{
			bool have_path=0;
			while(1){
				while(!q.empty()){
					auto [v,o]=q.front();q.pop();

					if(o==0){int x=v;
						//extend x\in L
						//printf("extend x %d\n",x);
						//inL[x]=1;
						//Dx[x]=Delta;
	
						//find all x..y
						for(auto [y,eid]:EX[x])if(!inR[y] && !inD[eid]){//y not in forest
							//try to augment x..y
							if(lx[x]+ly[y]!=w[eid]+!inD[eid]){//ineligible
								add_edge_to_bucket(w[eid]+!inD[eid]-lx[x]-ly[y]+Dx[x],x,y);
							}else{
								//add y to forest: R+=y
								//printf("R+=%d Dy[y]=%d\n",y,Delta);
								inR[y]=1;
								Dy[y]=Delta;
								q.push({y,1});
								if(dy[y]<cy[y]){
									have_path=1;//return;
								}
							}
						}
					}else{int y=v;
						//printf("extend y %d\n",y);
						//inR[y]=1;
						//Dy[y]=Delta;

						//find all y__x
						for(auto [x,eid]:EY[y])if(!inL[x] && inD[eid]){
							if(lx[x]+ly[y]!=w[eid]+!inD[eid]){//ineligible
								add_edge_to_bucket(lx[x]+ly[y]-(w[eid]+!inD[eid])+Dy[y],x,y);
							}else{
								//add x to forest: L+=x
								//printf("L+=%d Dx[x]=%d\n",x,Delta);
								inL[x]=1;
								Dx[x]=Delta;
								q.push({x,0});
							}
						}
					}
				}

				if(have_path)return;
				//printf("forest no path\n");
																	
				//now forest can't augment
				//find d to adjust
				auto upd_Delta=[&]()->void{
					while(Delta+1<bucket.size()){
						Delta++;
						//lx[L]++ ly[R]--
						//then label[LR] not change
						//	so our forest must contain them all
						//some ineligible L\bar{R} \bar{L}R may become eligible
						bool find_min_delta=0;
						for(auto [x,y]:bucket[Delta])if(!inR[y]){
							find_min_delta=1;
							//now x..y is eligible
	
							//add y to forest: R+=y
							//printf("R+=%d Dy[y]=%d\n",y,Delta);
							inR[y]=1;
							Dy[y]=Delta;
							q.push({y,1});

							if(dy[y]<cy[y]){
								have_path=1;//return;
							}
						}else if(!inL[x]){
							find_min_delta=1;
							//now y__x is eligible

							//add x to forest: L+=x
							//printf("L+=%d Dx[x]=%d\n",x,Delta);
							inL[x]=1;
							Dx[x]=Delta;
							q.push({x,0});
						}
						if(find_min_delta)return;
					}
					printf("error: out of bucket size\n");ffl;
					assert(0);
				};
				
				upd_Delta();
				//now q has new vertices
				//if(have_path)return;
			}
		};

		create_augmenting_path();

		//printf("Delta=%d\n",Delta);
		if(Delta==0)more_sz=1;
		
		for(int x=0;x<nx;x++)if(inL[x])lx[x]+=Delta-Dx[x];
		for(int y=0;y<ny;y++)if(inR[y])ly[y]-=Delta-Dy[y];
		//printf("bucket size = %d\n",(int)bucket.size());
		//maxBucketSize=max(maxBucketSize,(int)bucket.size());
		printDiffW();
	}

	void ScaleDCS(){//O(m*sqrt(n))
		//xy.assign(nx,{-1,0});
		//yx.assign(ny,{-1,0});
		inD.assign(m+1,0);
		dx.assign(nx,0);
		dy.assign(ny,0);
		sz=0;
		for(int x=0;x<nx;x++){
			for(auto [y,eid]:EX[x])if(w[eid]-lx[x]-ly[y]<-1){
				dx[x]++;dy[y]++;sz++;
				//printf("%d: [%d](%d/%d) (%d/%d)[%d] w[%d]=%d\n",sz,x,dx[x],cx[x],dy[y],cy[y],y,eid,w[eid]);ffl; 
				assert(dx[x]<=cx[x]);
				assert(dy[y]<=cy[y]);
				inD[eid]=1;
			}
		}
		//printf("sz=%d\n",sz);
		more_sz=0;
		while(!AugDCS()){//while not perfect
			Hungarian();
		}
	}

	void print_DCS(){
		return;
		ll ans=0;
		int i=0;
		for(int x=0;x<nx;x++){
			for(auto [y,eid]:EX[x])if(inD[eid]){
				ans+=w[eid];
				printf("%d: %d(%d)--< %d:%lld/%lld >--(%d)%d\n",++i,x,dx[x],eid,w[eid],weight[eid],dy[y],y);ffl;
				assert(dx[x]<=cx[x]);
				assert(dy[y]<=cy[y]);
			}
		}
		printf("mid DCS ans=%lld\n",ans);
	}

	void print_PDCS(){
		ll ans=0;
		int i=0;
		for(int x=0;x<nx;x++){
			for(auto [y,eid]:EX[x])if(inD[eid]){
				ans+=w[eid];
				printf("%d: %d(%d)--< %d:%lld/%lld >--(%d)%d\n",++i,x,dx[x],eid,w[eid],weight[eid],dy[y],y);ffl;
				assert(dx[x]==cx[x]);
				assert(dy[y]==cy[y]);
			}
		}
		printf("round DCS ans=%lld\n",ans);
	}

	void run(bool mx){//maximum weight perfect matching
		wtype ma=n/2+1; 
		if(mx)ma=-ma; 
		magnify(ma); 
		int L; 
		//N>=1
		L=__lg(N)+1;
		//w has L bits
		print();
		print_graph();
		printf("N=%lld L=%d\n",N,L);
		//maxBucketSize=0;

		for(int tt=1;tt<=L;tt++){
			for(int x=0;x<nx;x++)lx[x]=lx[x]*2-1;
			for(int y=0;y<ny;y++)ly[y]=ly[y]*2-1;
			w.clear();
			for(auto W:weight)w.pb(sign(W)*(abs(W)>>(L-tt)));
			//printf("round %d:\n",tt);
			printDiffW();
			ScaleDCS();
			//print_PDCS();
			//printf("max bucket size = %d\n",maxBucketSize);
		}
		
		//ll ans=0;
		int i=0;
		for(int x=0;x<nx;x++){
			for(auto [y,eid]:EX[x])if(inD[eid]){
				weight[eid]/=ma;
				//ans+=weight[eid];
				assert(dx[x]==cx[x]);
				assert(dy[y]==cy[y]);
				//printf("%d: (%d)--< %lld >--(%d)\n",++i,x,weight[eid],y);
			}
		}
		//printf("MWPDCS ans=%lld\n",ans);
		//printf("max bucket size = %d\n",maxBucketSize);
	}
};

struct BasicGreedy{
	int nx,ny,n,m;
	bool mx;
	wtype N;
	vector<vector<pii>>EX,EY;//[v,eid]
	vector<wtype>weight;
	vedge Eid;
	vector<pii>cx,cy;//l,r
	vint dx,dy;

	int _isolatedx_,_isolatedy_;
	ll ans;

	BasicGreedy(EWDCBG&G):nx(G.nx),ny(G.ny),m(G.m),EX(G.EX),EY(G.EY),N(G.N),weight(G.weight),cx(G.cx),cy(G.cy){
		n=nx+ny;
	}

	void printAns(){
		printf(">>>> BscGd ans=%lld _isolatedx_=%d _isolatedy_=%d\n",ans,_isolatedx_,_isolatedy_);
	}

	void run(){
		Eid.clear();
		for(int x=0;x<nx;x++){
			for(auto [y,eid]:EX[x]){
				Eid.pb({eid,x,y});
			}
		}
		sort(Eid.begin(),Eid.end(),[&](piii u,piii v){
			return weight[u[0]]>weight[v[0]];
		});
		dx.clear(); dx.resize(nx);
		dy.clear(); dy.resize(ny);
		ans=0;
		for(auto [eid,x,y]:Eid){
			if(dx[x]<cx[x][1] && dy[y]<cy[y][1]){
				dx[x]++;
				dy[y]++;
				//printf("%d: [%d](%d)--< %lld >--(%d)[%d]\n",i,dx[x],x,weight[eid],y,dy[y]);
				ans+=weight[eid];
			}
		}
		_isolatedx_=0,_isolatedy_=0;
		for(int x=0;x<nx;x++)
			if(dx[x]==0)_isolatedx_++;
		for(int y=0;y<ny;y++)
			if(dy[y]==0)_isolatedy_++;
		//for(int x=0;x<nx;x++)printf("%d:[%d,%d,%d]\n",x,cx[x][0],dx[x],cx[x][1]);
		//for(int y=0;y<ny;y++)printf("[%d,%d,%d]:%d\n",cy[y][0],dy[y],cy[y][1],y);
		printAns();ffl;
	}
};

struct MWDCS{//
	int nx,ny,n,m;
	bool mx;
	wtype N;
	vector<vector<pii>>EX,EY;//[v,eid]
	vector<wtype>weight;
	EWDCBG H;
	vector<pii>cx,cy;//l,r
	vint dx,dy;

	int _isolatedx_,_isolatedy_;
	ll ans;

	MWDCS(EWDCBG&G):nx(G.nx),ny(G.ny),EX(G.EX),EY(G.EY),N(G.N),weight(G.weight),cx(G.cx),cy(G.cy){
		n=nx+ny;
		H=EWDCBG(n,n);
		m=G.m; assert(weight.size()==m+1);
		H.weight=weight;
		H.cx=cx; H.cy=cy;
		for(int i=1;i<=m;i++)H.weight.pb(weight[i]);
		//cout<<cx.size()<<" "<<cy.size()<<endl;
		for(int x=0;x<nx;x++){
			H.cy.pb(cx[x]);
			for(auto [y,eid]:EX[x]){
				H.EX[x].pb({y,eid});
				H.EX[nx+y].pb({ny+x,m+eid});
			}
		}

		m+=m;

		int two_m=m;

		for(int x=0;x<nx;x++){
			for(int i=cx[x][0]+1;i<=cx[x][1];i++){
				H.weight.pb(0);
				H.EX[x].pb({ny+x,++m});
			}
		}

		for(int y=0;y<ny;y++){
			H.cx.pb(cy[y]);
			for(int i=cy[y][0]+1;i<=cy[y][1];i++){
				H.weight.pb(0);
				H.EX[nx+y].pb({y,++m});
			}
		}
		printf("add %d 0-edges\n",(int)H.weight.size()-two_m-1);
		H.EXY();

		H.N=N; H.m=m; 
		assert(H.cx.size()==n);
		assert(H.cy.size()==n);
		//for(int x=0;x<n;x++)printf("%d:[%d,%d]\n",x,H.cx[x][0],H.cx[x][1]);
		//for(int y=0;y<n;y++)printf("[%d,%d]:%d\n",H.cy[y][0],H.cy[y][1],y);

		printf("doubled G\n");
	}

	void printAns(){
		printf(">>>> MWDCS ans=%lld _isolatedx_=%d _isolatedy_=%d\n",ans,_isolatedx_,_isolatedy_);
	}

	void run(){
		MWPDCS DOD(H);
		DOD.run(mx);
		dx.clear(); dx.resize(nx);
		dy.clear(); dy.resize(ny);
		int i=0;
		ans=0;
		for(int x=0;x<nx;x++){
			for(auto [y,eid]:EX[x])if(DOD.inD[eid]){
				ans+=weight[eid];
				dx[x]++;dy[y]++;
				assert(dx[x]<=cx[x][1]);
				assert(dy[y]<=cy[y][1]);
				//printf("%d: [%d](%d)--< %lld >--(%d)[%d]\n",++i,dx[x],x,weight[eid],y,dy[y]);
			}
		}
		_isolatedx_=0,_isolatedy_=0;
		for(int x=0;x<nx;x++)
			if(dx[x]==0)_isolatedx_++;
		for(int y=0;y<ny;y++)
			if(dy[y]==0)_isolatedy_++;
		//for(int x=0;x<nx;x++)printf("%d:[%d,%d,%d]\n",x,cx[x][0],dx[x],cx[x][1]);
		//for(int y=0;y<ny;y++)printf("[%d,%d,%d]:%d\n",cy[y][0],dy[y],cy[y][1],y);
		printAns();ffl;
	}
};

wtype MWDCSW(EWDCBG&G){
	wtype W=0;
	for(int x=0;x<G.nx;x++){
		set<pair<wtype,int>>st;//w,eid
		for(auto [y,eid]:G.EX[x])if(G.weight[eid]>0){
			st.insert({G.weight[eid],eid});
			if(st.size()>G.cx[x][1]){
				st.erase(st.begin());
			}
		}
		for(auto [w,eid]:st)W+=max(0ll,w);
	}
	printf("MWDCSW=%lld\n",W);
	return W;
}

struct FIMWS{
	int nx,ny,n,m;
	bool mx;
	wtype N,W;
	vector<vector<pii>>EX,EY;//[v,eid]
	vector<wtype>weight;
	EWDCBG H;
	vint cx,cy;//vertex capacity
	vint dx,dy;

	int _isolatedx_,_isolatedy_;
	ll ans;

	FIMWS(EWDCBG&G):nx(G.nx),ny(G.ny),EX(G.EX),EY(G.EY),N(G.N),weight(G.weight){
		W=2*MWDCSW(G)+1;

		cx.clear(); cx.resize(nx);
		cy.clear(); cy.resize(ny);
		for(int x=0;x<nx;x++)cx[x]=G.cx[x][1];
		for(int y=0;y<ny;y++)cy[y]=G.cy[y][1];
		n=nx+ny;
		H=EWDCBG(n,n);
		m=G.m; assert(weight.size()==m+1);
		H.weight=weight;
		H.cx=G.cx; H.cy=G.cy;
		for(int i=1;i<=m;i++)H.weight.pb(weight[i]);
		//cout<<cx.size()<<" "<<cy.size()<<endl;
		for(int x=0;x<nx;x++){
			H.cy.pb(H.cx[x]);
			for(auto [y,eid]:EX[x]){
				H.EX[x].pb({y,eid});
				H.EX[nx+y].pb({ny+x,m+eid});
			}
		}

		m+=m;

		int two_m=m;

		for(int x=0;x<nx;x++){
			H.weight.pb(-W);
			H.EX[x].pb({ny+x,++m});
			for(int i=2;i<=cx[x];i++){
				H.weight.pb(0);
				H.EX[x].pb({ny+x,++m});
			}
		}

		for(int y=0;y<ny;y++){
			H.cx.pb(H.cy[y]);
			H.weight.pb(-W);
			H.EX[nx+y].pb({y,++m});
			for(int i=2;i<=cy[y];i++){
				H.weight.pb(0);
				H.EX[nx+y].pb({y,++m});
			}
		}
		printf("add %d 0-edges\n",(int)H.weight.size()-two_m-1);
		H.EXY();

		H.N=max(N,W); H.m=m; 
		assert(H.cx.size()==n);
		assert(H.cy.size()==n);
		//for(int x=0;x<n;x++)printf("%d:[%d,%d]\n",x,H.cx[x][0],H.cx[x][1]);
		//for(int y=0;y<n;y++)printf("[%d,%d]:%d\n",H.cy[y][0],H.cy[y][1],y);

		printf("doubled G\n");
	}

	void printAns(){
		printf(">>>> FIMWS ans=%lld _isolatedx_=%d _isolatedy_=%d\n",ans,_isolatedx_,_isolatedy_);
	}

	void run(){
		MWPDCS DOD(H);
		DOD.run(mx);
		dx.clear(); dx.resize(nx);
		dy.clear(); dy.resize(ny);
		int i=0;
		ans=0;
		for(int x=0;x<nx;x++){
			for(auto [y,eid]:EX[x])if(DOD.inD[eid]){
				ans+=weight[eid];
				dx[x]++;dy[y]++;
				assert(dx[x]<=cx[x]);
				assert(dy[y]<=cy[y]);
				//printf("%d: [%d](%d)--< %lld >--(%d)[%d]\n",++i,dx[x],x,weight[eid],y,dy[y]);
			}
		}
		_isolatedx_=0,_isolatedy_=0;
		for(int x=0;x<nx;x++)
			if(dx[x]==0)_isolatedx_++;
		for(int y=0;y<ny;y++)
			if(dy[y]==0)_isolatedy_++;
		//for(int x=0;x<nx;x++)printf("%d:[%d,%d,%d]\n",x,cx[x][0],dx[x],cx[x][1]);
		//for(int y=0;y<ny;y++)printf("[%d,%d,%d]:%d\n",cy[y][0],dy[y],cy[y][1],y);
		printAns();ffl;
	}
};

struct MCMF{
	int S,T,k;
	vint z;// last eid
	vector<wtype>dist;
	vint pre;
	int maxflow;
	wtype mincost;
	struct edge{
		wtype w;//weight(cost)
		int x,t,c;//next, to, capacity
	};
	vector<edge>e;//e[eid] & e[eid^1] 
	MCMF(){
		k=1;
		e.clear(); 
		e.resize(2);
		z.clear();
		maxflow=0;
		mincost=0;
	}
	void add(int u,int v,int c,wtype w){
		//printf("+%d %d %d %lld\n",k+1,u,v,w);
		e.pb({w,z[u],v,c});
		z[u]=++k; 
		e.pb({-w,z[v],u,0});
		z[v]=++k; 
	}

	bool dijk(){
		priority_queue<pair<wtype,int>,vector<pair<wtype,int>>,greater<>>q;
		q.push({0,S});
		dist.assign(T+1,LLONG_MAX);
		dist[S]=0;
		pre.assign(T+1,0);
		while(q.size()){
			auto [d,u]=q.top();q.pop();
			if(d>dist[u])continue;
			for(int i=z[u];i;i=e[i].x)if(e[i].c){
				int v=e[i].t;
				if(dist[v]>dist[u]+e[i].w){
					dist[v]=dist[u]+e[i].w;
					pre[v]=i;
					q.push({dist[v],v});
				}
			}
		}
		//cout<<dist[T]<<endl;
		return dist[T]<LLONG_MAX;
	}

	void run(){
		while(dijk()){
			maxflow++;
			int u=T;
			while(pre[u]){//cout<<u<<' ';
				int i=pre[u];
				e[i].c--;
				e[i^1].c++;
				mincost+=e[i].w;
				u=e[i^1].t;
			}
			//pun;
			//printf("mincost=%lld\n",mincost);
		}
	}
};

struct MWMME{
	wtype ans;
	int nx,ny;
	vint dx,dy;
	int _isolatedx_,_isolatedy_;

	MWMME(){

	}

	MWMME(EWBG&G):nx(G.nx),ny(G.ny){//want Y max
		MCMF F;
		F.S=G.nx+G.ny+1; 
		F.T=F.S+1;
		F.z.resize(F.T+1);//last eid
		for(int x=0;x<G.nx;x++){
			F.add(F.S,x,1,0);
			for(auto [y,w]:G.EX[x]){
				F.add(x,G.nx+y,1,-w);//max weight -> min cost
			}
		}
		for(int y=0;y<G.ny;y++){
			F.add(G.nx+y,F.T,1,0);
		}
	}

	void printAns(){
		printf(">>>> MWMME ans=%lld _isolatedx_=%d _isolatedy_=%d\n",ans,_isolatedx_,_isolatedy_);
	}

	void MWYMME(EWDCBG&G){//want Y max
		nx=G.nx;ny=G.ny;
		MCMF F;
		F.S=G.nx+G.ny+1; 
		F.T=F.S+1;
		F.z.resize(F.T+1);//last eid
		vint eidGtF(G.m+1);
		vint eidxc(G.nx);
		dx.resize(nx);
		dy.resize(ny);
		for(int x=0;x<G.nx;x++){
			F.add(F.S,x,G.cx[x][1],0);//x's capacity
			eidxc[x]=F.k;
			for(auto [y,eid]:G.EX[x]){
				F.add(x,G.nx+y,1,-G.weight[eid]);//max weight -> min cost
				eidGtF[eid]=F.k;
			}
		}
		for(int y=0;y<G.ny;y++){
			F.add(G.nx+y,F.T,1,0);
		}
		//cout<<F.S<<" "<<F.T<<endl;
		F.run();
		//cout<<F.maxflow<<" "<<F.mincost<<endl;
		ans=-F.mincost;

		set<edge>st;//w,x,y
		//if take eid, then F.e[eidGtF[eid]].c>0
		for(int x=0;x<G.nx;x++){
			//x take max c[x][1]-dx[x] edges
			dx[x]=F.e[eidxc[x]].c;
			//printf("dx[%d]=%d/%d\n",x,dx[x],G.cx[x][1]);	
			for(auto [y,eid]:G.EX[x])if(F.e[eidGtF[eid]].c==0){//have rev
				st.insert({G.weight[eid],x,y});
				//if(st.size()>G.cx[x][1]-dx[x]){
				//	st.erase(st.begin());
				//}
			}else{
				dy[y]++;
				//printf("x %d y %d [%d]=%lld\n",x,y,eid,G.weight[eid]);
			}
		}
		for(auto [w,x,y]:st)if(dx[x]<G.cx[x][1] && dy[y]<G.cy[y][1]){
			//printf("x %d y %d %lld\n",x,y,w);
			ans+=w;//weight>=0
			//cout<<ans<<endl;
			dy[y]++;
			dx[x]++;
		}
		//cout<<ans<<endl;

		_isolatedx_=0,_isolatedy_=0;
		for(int x=0;x<nx;x++)
			if(dx[x]==0)_isolatedx_++;
		for(int y=0;y<ny;y++)
			if(dy[y]==0)_isolatedy_++;

		printAns();ffl;
	}

	void MWPM(EWDCBG&G){//want Y max
		nx=G.nx;ny=G.ny;
		int n=nx+ny;
		/*EWBG G_(G);
		MWMM M(G_);
		M.run();
		
		ans=M.ans;

		//if take eid, then F.e[eidGtF[eid]].c>0
		for(int x=0;x<G.nx;x++){
			//x take max c[x][1]-dx[x] edges
			dx[x]=F.e[eidxc[x]].c;
			set<pair<wtype,int>>st;//w,y
			for(auto [y,eid]:G.EX[x])if(F.e[eidGtF[eid]].c==0){//have rev
				st.insert({G.weight[eid],y});
				if(st.size()>G.cx[x][1]-dx[x]){
					st.erase(st.begin());
				}
			}else{
				dy[y]++;
				//printf("x %d y %d [%d]=%lld\n",x,y,eid,G.weight[eid]);
			}
			for(auto [w,y]:st){
				//printf("x %d y %d %lld\n",x,y,w);
				ans+=w;//weight>=0
				//cout<<ans<<endl;
				dy[y]++;
				dx[x]++;
			}
		}
		//cout<<ans<<endl;

		_isolatedx_=0,_isolatedy_=0;
		for(int x=0;x<nx;x++)
			if(dx[x]==0)_isolatedx_++;
		for(int y=0;y<ny;y++)
			if(dy[y]==0)_isolatedy_++;*/

		printAns();ffl;
	}

};

int main(){
	/*{
		EWBG G(5,7);
		G.random_graph_d_min(15,10);
		G.print_graph();
		
		MWM A(G);
		A.mx=0;A.run();
		A.mx=1;A.run();
	}*/

	/*{
		EWDCBG G;
		G.read();
		MWDCS A(G);
		A.mx=0;A.run();
		A.mx=1;A.run();
	}*/

	{	
		//int nx=5,ny=7,_e_=15,_N_=10;//test0
		//int nx=5,ny=7,_e_=70,_N_=10;//test0
		//int nx=2,ny=3,_e_=6,_N_=10;
		//int nx=2,ny=3,_e_=30,_N_=10;
		//int nx=100,ny=300,_e_=6000,_N_=100;//test1
		//int nx=1000,ny=3000,_e_=60000,_N_=100;//test2
		//int nx=1000,ny=3000,_e_=10000,_N_=100;//test21
		//int nx=1000,ny=3000,_e_=40000,_N_=100;//test22
		//int nx=3000,ny=9000,_e_=100000,_N_=100;//test31
		//int nx=10000,ny=30000,_e_=100000,_N_=100;//test3
		int nx=30000,ny=90000,_e_=300000,_N_=100;//test4
		//int nx=100000,ny=300000,_e_=1000000,_N_=100;//test5
		//int nx=200000,ny=600000,_e_=1000000,_N_=100;//test6
		//int nx=200000,ny=600000,_e_=2000000,_N_=100;//test7
		//int nx=500000,ny=1500000,_e_=5000000,_N_=100;//test8
		//int nx=500000,ny=1500000,_e_=10000000,_N_=100;//test9
		//int nx=1000000,ny=3000000,_e_=10000000,_N_=100;//testa
		
		EWDCBG G(nx,ny);
		//G.random_graph_d_min(_e_,_N_);
		G.random_graph_p_d_max(_e_,_N_);
		G.print_graph();
		
		vpii cx(nx),cy(ny);
		for(int x=0;x<nx;x++)cx[x]={0,min((int)G.EX[x].size(),int(1+rng()%15))};
		for(int y=0;y<ny;y++)cy[y]={0,(int)G.EY[y].size()};

		//for(int x=0;x<nx;x++)printf("%d:[%d,%d]\n",x,cx[x][0],cx[x][1]);
		//for(int y=0;y<ny;y++)printf("[%d,%d]:%d\n",cy[y][0],cy[y][1],y);

		G.cx=cx; G.cy=cy;

		time_t now;

		now=time(nullptr);
		BasicGreedy BG(G);
		//A.mx=0;A.run();
		BG.mx=1;BG.run();
		time_t BGtm=time(nullptr)-now;

		now=time(nullptr);
		MWDCS A(G);
		//A.mx=0;A.run();
		A.mx=1;A.run();
		time_t Atm=time(nullptr)-now;		

		now=time(nullptr);
		FIMWS B(G);
		B.mx=1;B.run();
		time_t Btm=time(nullptr)-now;

		now=time(nullptr);
		MWMME M;
		M.MWYMME(G);
		time_t Mtm=time(nullptr)-now;

		pun;

		BG.printAns();
		std::cout<<BGtm<<"s"<<std::endl;
		A.printAns();
		std::cout<<Atm<<"s"<<std::endl;
		B.printAns();
		std::cout<<Btm<<"s"<<std::endl;
		M.printAns();
		std::cout<<Mtm<<"s"<<std::endl;

		printf("BscGd ans=%.4lf isolated=%.4lf\n",(double)BG.ans/A.ans,(double)BG._isolatedy_/G.ny);
		printf("MWDCS ans=1 isolated=%.4lf\n",(double)A._isolatedy_/G.ny);
		printf("MWMME ans=%.4lf isolated=%.4lf\n",(double)M.ans/A.ans,(double)M._isolatedy_/G.ny);
		printf("FIMWS ans=%.4lf isolated=%.4lf\n",(double)B.ans/A.ans,(double)B._isolatedy_/G.ny);
	}

	return 0;
}
