//constraints:
//must pass vertex and edges
//can't pass edges
//upper bound vertex
//less path distance
#include <bits/stdc++.h>

using namespace std;

typedef long long LL;
#define TIME
const int N = 1001;
const int E = 5000;
const int INF = 1000000000;
const int DPSEC = 100001;

FILE *fin = fopen("data.txt","r");
FILE *fout = fopen("out.txt","w");
struct Edge{
    int u,v;
    Edge(){}
    Edge(int u,int v):u(u),v(v){}
    getEdge(){//guarantee order
        fscanf(fin,"%d%d",&u,&v);
        if (u>v) swap(u,v);
    }
};
struct MaskOrder{
    int cnt;
    int sz[N];//一维检索
    int jz[N][N];//二维检索
    pair<int,int> fIndex[N];//新的编号对应原来的边或者点
    MaskOrder(){
        cnt = 0;
        memset(sz,0,sizeof sz);
        memset(jz,0,sizeof jz);
    }
    void insertEdge(int u,int v){
        cnt++;
        jz[u][v] = jz[v][u] = cnt;
        fIndex[cnt] = make_pair(u,v);
    }
    void insertEdge(Edge edge){
        insertEdge(edge.u, edge.v);
    }
    void insertVertex(int u){
        cnt++;
        sz[u] = cnt;
        fIndex[cnt] = make_pair(u,-1);
    }
    int findEdge(int u,int v){
        return jz[u][v];
    }
    int findVertex(int u){
        return sz[u];
    }
    pair<int,int> findIndex(int index){
        return fIndex[index];
    }
};
struct Node{
    int v,w;
    Node(){}
    Node(int v,int w):v(v),w(w){}
};
MaskOrder maskOrder;
int n,m,mustPassVertexesNum,mustPassEdgesNum,cannotPassEdgesNum,canPassVertexesNum;
int vertexBound;
vector<Node> link[N];
int mustPassVertexes[N];
Edge mustPassEdges[E];
int maxMask,bound;
int jz[N][N];//jz 矩阵

struct QZ{//权重 ,less is better
    double xs[4]={0.266371,0.221976,0.372919,0.138735};
    int a[4];
    double b[4],c[4];
    int mNum[4];//经过的点数(less)，必经点经过的点数(more)，必经边经过的条数(more)，路径长度(less)
    QZ(){
        mNum[0]=1;mNum[3]=1;mNum[1]=mNum[2]=1;
    }
    void setXS(){
        //四个约束条件（1经过的点数，2必经点经过的点数，3必经边经过的条数，4路径长度）的序关系（如 1 3 4 2）表示1>3>4>2
        for (int i=0;i<4;i++)fscanf(fin,"%d",&a[i]),a[i]--;
        for (int i=0;i<3;i++)fscanf(fin,"%lf",&b[i+1]);

        double sum=0;
        for (int i=1;i<4;i++){
                double t = 1;
                for(int j=i;j<4;j++) t*=b[j];
                sum+=t;
        }
        c[3] = 1/(1.0+sum);
        c[2] = c[3] * b[3];
        c[1] = c[2] * b[2];
        c[0] = c[1] * b[1];
        for (int i=0;i<4;i++)xs[a[i]] = c[i];
    }
    void setMNum(int havePassVertex,int mustPassVertexesNum,int mustPassEdgesNum,int dis){
        mNum[3] = max(mNum[3], dis); //参考路径长度设为所有求得的路径中的最大值
    }
    void setMNum(){
        mNum[0] = canPassVertexesNum;
        mNum[1] = mustPassVertexesNum;
        mNum[2] = mustPassEdgesNum;
    }
    double value(int havePassVertex,int mustPassVertexesNum,int mustPassEdgesNum,int dis){
        return xs[0]*(havePassVertex-mNum[0])/mNum[0]+xs[1]*(-mustPassVertexesNum+mNum[1])/mNum[1]+xs[2]*(-mustPassEdgesNum+mNum[2])/mNum[2]+xs[3]*(dis-mNum[3])/mNum[3];
    }
};
QZ qz;

int addAns = 0;//after branchCut, ans need add
int markVertex[N];// markVertex[i] = 1, then delete i
void branchCut(){//cut useless branch
    memset(markVertex,0,sizeof markVertex);

    queue<int>Q; while (!Q.empty())Q.pop();
    int d[N] = {} , vi[N] = {};//du
    //vi[i] = 1表示i已经进入队列或者删除
    for (int i = 1; i < n-1; i++) for (int j = 1; j < n-1; j++) if (jz[i][j] != INF) d[i]++;//start,end not change
    for (int i = 1; i < n-1; i++){
        if (d[i] == 0){
            markVertex[i] = 1; vi[i] = 1;
        }else if ((d[i] == 1 || d[i] == 2) && !maskOrder.findVertex(i) ){
            Q.push(i); vi[i] = 1;
        }
    }
    while (!Q.empty()){
        int u = Q.front(); Q.pop();

        if (d[u] == 0) continue;
        if (d[u] == 1 || d[u] == 2){
            for (int i = 1; i < n-1; i++) if (jz[u][i] != INF){
                if (!maskOrder.findVertex(u) && !maskOrder.findVertex(i)){
                    jz[u][i] = jz[i][u] = INF;
                    d[i]--;d[u]--;
                    if ((1 == d[i] || d[i] == 2) && !vi[i]){
                        Q.push(i);vi[i] = 1;
                    }
                    if (!d[i]) markVertex[i] = 1;
                    if (!d[u]) {markVertex[u] = 1; break; }
                }

            }
        }
    }
}
void init(){//get data
    qz.setXS();//设置系数
    //n vertex , m edges , must pass vertex , must pass edges, can't pass edges
    fscanf(fin,"%d%d%d",&n,&m,&canPassVertexesNum);

    for (int i = 0; i < n; i++)
        for (int j = 0 ; j < n; j++)
            jz[i][j] = INF;
    for (int i = 0; i < m; i++){
        int u,v,w;fscanf(fin,"%d%d%d",&u,&v,&w);
        if (w<jz[u][v]) jz[u][v] = jz[v][u] = w;//same edges get the min edge
    }
    for (int i = 0; i < n; i++) jz[i][i] = INF ;// self-loop
    fscanf(fin,"%d",&mustPassVertexesNum);
    for (int i = 0; i < mustPassVertexesNum; i++){
        fscanf(fin,"%d",&mustPassVertexes[i]);
        maskOrder.insertVertex(mustPassVertexes[i]);//order
    }

    fscanf(fin,"%d",&mustPassEdgesNum);
    for (int i = 0; i < mustPassEdgesNum; i++){
        mustPassEdges[i].getEdge();
        maskOrder.insertEdge(mustPassEdges[i]);//order
    }

    fscanf(fin,"%d",&cannotPassEdgesNum);
    for (int i = 0; i < cannotPassEdgesNum; i++){
        int u,v;fscanf(fin,"%d%d",&u,&v);
        jz[u][v] = jz[v][u] = INF;//delete edges
    }

    branchCut();
    for (int i = 0; i < n; i++) link[i].clear();
    for (int i = 0; i < n; i++)if (!markVertex[i]){
        for (int j = 0; j < n; j++)if (!markVertex[j] && jz[i][j] != INF){
                link[i].push_back(Node(j,jz[i][j]));
        }
    }
    fclose(fin);
}
struct EnumDp{ //dp's enum动态规划的状态枚举
    int u,havePassVertex,mask;
    int value;
    EnumDp(){}
    EnumDp(int u, int havePassVertex, int mask,int value):u(u),
                    havePassVertex(havePassVertex),mask(mask),value(value){}
    bool operator < (const EnumDp& A)const{
        return (havePassVertex>A.havePassVertex)||((havePassVertex == A.havePassVertex) && (value>A.value));
    }
};
priority_queue<EnumDp> Q;
int dp[N][DPSEC];
bool vis[N][DPSEC];
int lastU[N][DPSEC];
int lastMask[N][DPSEC];
int hashDp(int x,int y){return x*(maxMask+1)+y;}
void dijkstra(){
    //dp[i][havePassVertex][mask]
    while (!Q.empty()) Q.pop();
    for (int i= 0; i< n; i++)
        for (int j= 0;j <= min(DPSEC-1, vertexBound * (1<<(maskOrder.cnt))) ; j++)
                dp[i][j] = INF ,vis[i][j] = 0;

    //cout<<min(DPSEC, vertexBound * (1<<(maskOrder.cnt)))<<endl;
    int index = maskOrder.findVertex(0); //判断0 是不是必须经过的节点
    index = index? 1<<(index-1): 0;
    dp[0][hashDp(1,index)] = 0;
    Q.push(EnumDp(0,1,index,0));

    while (!Q.empty()){
        EnumDp enumDp = Q.top(); Q.pop();
        int u = enumDp.u , havePassVertex = enumDp.havePassVertex, mask = enumDp.mask;
        if (vis[u][hashDp(havePassVertex,mask)])continue;
        vis[u][hashDp(havePassVertex,mask)] = 1;

        for (int i=0;i<link[u].size();i++){
            Node edge = link[u][i];
            int v = edge.v, w = edge.w;

            //get newMask
            int newMask = mask;
            index = maskOrder.findEdge(u,v);
            if (index) newMask |= 1<<(index-1);
            index = maskOrder.findVertex(v);
            if (index) newMask |= 1<<(index-1);

            int vHashDp = hashDp(havePassVertex+1,newMask), uHashDp = hashDp(havePassVertex,mask);
            if (dp[v][vHashDp] > dp[u][uHashDp] + w){
                dp[v][vHashDp] = dp[u][uHashDp] + w;
                lastU[v][vHashDp] = u;
                lastMask[v][vHashDp] = mask;

                if (havePassVertex < vertexBound){
                    if ((newMask == maxMask) && (v == n-1) ){
                        //printf("%d %d %d %d\n",v,havePassVertex+1,newMask,dp[v][vHashDp]);
                        vertexBound = min(vertexBound, int(havePassVertex * 1.618)); // 减少搜索范围
                        bound = max(bound, vertexBound);
                    }
                    /*if (v == n-1 && havePassVertex+1 == 389){
                        printf("%d %d %d %d %d\n",v,havePassVertex+1,newMask,vHashDp,dp[v][vHashDp]);
                    }*/
                    int d = dp[v][vHashDp];
                    Q.push(EnumDp(v,havePassVertex+1,newMask,d));
                }
            }
        }
    }
}
struct OtherSolver{
    typedef int ValDat ;
    struct EnumDp{ //enum动态规划的状态枚举
        int u,havePassVertex;
        ValDat value;
        EnumDp(){}
        EnumDp(int u, int havePassVertex ,ValDat value):u(u),
                        havePassVertex(havePassVertex),value(value){}
        bool operator < (const EnumDp& A)const{
            return (havePassVertex>A.havePassVertex)||((havePassVertex == A.havePassVertex) && (value>A.value));
        }
    };
    priority_queue<EnumDp> Q;
    EnumDp dist[10001];
    int vist[10001];
    int last[10001];
    int rec[10001],rech;
    void dijkstra(int u){
        while (!Q.empty()) Q.pop();
        for (int i=0;i<n;i++) dist[i].value = INF, vist[i] = 0;
        Q.push(dist[u] = EnumDp(u,1,0));
        while (!Q.empty()){
            EnumDp enumDp = Q.top(); Q.pop();
            int u = enumDp.u , havePassVertex = enumDp.havePassVertex;
            if (vist[u])continue;
            vist[u] = 1;
            for (int i=0;i<link[u].size();i++){
                Node edge = link[u][i];
                int v = edge.v, w = edge.w;

                if (dist[v].value > dist[u].value + w){
                    dist[v].value = dist[u].value + w;
                    last[v] = u;
                    Q.push(dist[v] = EnumDp(v,havePassVertex+1,dist[v].value));
                }
            }
        }
    }
    int markVertex[10001];//must Vertex
    int markEdge[10001];
    void dyuet(){
        memset(markEdge,0,sizeof markEdge);
        memset(markVertex,0,sizeof markVertex);

        mustPassVertexes[mustPassVertexesNum] = n-1;
		mustPassVertexesNum ++;

        int u = 0;markVertex[0] = 1;
        int haveE = 0,haveV = 0; ValDat haveDis = 0;
        rech=0;
        while (u != n-1){
            dijkstra(u);

            int k = -1;
            for (int i=0;i<mustPassVertexesNum;i++)if (!markVertex[i]){
                if (k==-1 || dist[mustPassVertexes[k]].value > dist[mustPassVertexes[i]].value){
					k = i;
				}
            }
            int kk = -1,v;
            for (int i=0;i<mustPassEdgesNum;i++)if (!markEdge[i]){
                if (mustPassEdges[i].u == u){
                    if (kk==-1 || dist[v].value > dist[ mustPassEdges[i].v ].value){
                        kk = i;v=mustPassEdges[i].v;
                    }
                }
                if (mustPassEdges[i].v == u){
                    if (kk==-1 || dist[v].value > dist[ mustPassEdges[i].u ].value){
                        kk = i;v=mustPassEdges[i].u;
                    }
                }
            }
			if (k == -1 && kk == -1){
				fprintf(fout,"no answer!");exit(0);
			}
			if (kk != -1 && (k==-1 || dist[v].value < dist[mustPassVertexes[k]].value)){
                haveDis += dist[v].value;
                for (int i=0;i<mustPassVertexesNum;i++)if (!markVertex[i] && mustPassVertexes[i]==v){
                    haveV++;
                    markVertex[i]=1;
                    break;
                }
                haveE++;
                markEdge[kk]=1;
                rec[rech]=u;rech++;
                u = v;
			}else{
			    haveDis += dist[mustPassVertexes[k]].value;
                last[u]=-1;recPath(mustPassVertexes[k],haveE,haveV);rech--;
                u = mustPassVertexes[k];
			}
        }
        mustPassVertexesNum --;
        rec[rech]=n-1;rech++;
        fprintf(fout,"passVertex = %d\n",rech);
        fprintf(fout,"distance = %d\n",haveDis);
        int flag=0;fprintf(fout,"mustPassEdge = ");for (int i = 0;i< mustPassEdgesNum;i++) if (markEdge[i]) flag=1,fprintf(fout," {%d,%d} ",mustPassEdges[i].u,mustPassEdges[i].v);if (!flag)fprintf(fout,"NULL");fprintf(fout,"\n");
        flag=0;fprintf(fout,"mustPassVertex = ");for (int i = 0;i< mustPassVertexesNum;i++) if (markVertex[i]) flag=1,fprintf(fout," %d ",mustPassVertexes[i]);if (!flag)fprintf(fout,"NULL");fprintf(fout,"\n");
        fprintf(fout,"%d ",rec[0]);for (int i=1;i<rech;i++)fprintf(fout," => %d",rec[i]);fprintf(fout,"\n\n");
        return ;

    }
	void recPath(int u,int&haveE,int&haveV){
		if (u==-1){
			return ;
		}
		int v = last[u];
		for (int i=0;i<mustPassVertexesNum;i++)if (!markVertex[i] && mustPassVertexes[i]==u){
            haveV++;
            markVertex[i]=1;
		}
		for (int i=0;i<mustPassEdgesNum;i++)if (!markEdge[i] &&((mustPassEdges[i].u==u && mustPassEdges[i].v==v) || (mustPassEdges[i].u==v && mustPassEdges[i].v==u))){
            haveE++;
            markEdge[i]=1;
		}
		recPath(v,haveE,haveV);
		rec[rech]=u;rech++;
	}
    void solve(){
        dyuet();
    }
};
struct PRINT{
private :
    int ansCnt = 0;
public  :
    void printEdges(int x,int ed,int st){
        int cnt = 0;
        fprintf(fout,"pass must edges = ");
        for (int i=ed;i>=st;i--)if (x>>(i-1)&1){
                pair<int,int> f = maskOrder.findIndex(i);
                cnt++;
                if (cnt>1) fprintf(fout," ,");
                fprintf(fout," {%d,%d}",f.first,f.second);
        }
        if (!cnt) fprintf(fout,"NULL");
        fprintf(fout,"\n");
    }
    void printMask(int x,int n){fprintf(fout,"mask = ",x);for (int i=n-1;i>=0;i--)fprintf(fout,"%d",x>>i&1);fprintf(fout,"\n");}
    void printVertexes(int x,int ed,int st){
        int cnt = 0;
        fprintf(fout,"pass must Vertexes = ");
        for (int i=ed;i>=st;i--)if (x>>(i-1)&1){
                pair<int,int> f = maskOrder.findIndex(i);
                cnt++;
                if (cnt>1) fprintf(fout," ,");
                fprintf(fout," %d",f.first);
        }
        if (!cnt) fprintf(fout,"NULL");
        fprintf(fout,"\n");
    }
    void printPath(int u,int havePassVertex,int mask){
        if (havePassVertex == 1){
            fprintf(fout,"%d",u);
            return ;
        }

        int uHashDp = hashDp(havePassVertex,mask);
        printPath(lastU[u][uHashDp],havePassVertex-1,lastMask[u][uHashDp]);
        fprintf(fout," => %d",u);
    }
    void printAll(int n,int havePassVertex,int mask,int flag){ // flag = 1, is reference path
        if (havePassVertex == -1){
            if (!flag)fprintf(fout,"No path!\n");return ;
        }
        if ((ansCnt >= 14 || vis[n][hashDp(havePassVertex,mask)]) && flag) return ;

        if (dp[n][hashDp(havePassVertex,mask)] == INF){
            if (!flag)fprintf(fout,"No path!\n");return ;
        }
        vis[n][hashDp(havePassVertex,mask)] = 1;
        fprintf(fout,"passVertex = %d\n",havePassVertex);
        fprintf(fout,"distance = %d\n",dp[n][hashDp(havePassVertex,mask)]); //printf("%d %d %d\n",n,havePassVertex,mask);//
        printEdges(mask,maskOrder.cnt,mustPassVertexesNum+1);
        printVertexes(mask,mustPassVertexesNum,1);
        printPath(n,havePassVertex,mask);fprintf(fout,"\n\n");
        ansCnt++;
        return ;
    }
    void printNoConstraints(){
        fprintf(fout,"********No constraints**********\n");
        int besti = -1, bestDp = INF;
        for (int i = 0; i <= bound; i++){
            if (dp[n-1][hashDp(i,0)] < bestDp){
                bestDp = dp[n-1][hashDp(i,0)];
                besti = i;
            }
        }
        printAll(n-1,besti,0,0);
    }
    void printOnlyPassNumConstraints(){
        fprintf(fout,"********Only less equal max Pass Num Constraints********\n");//点限制
        int besti = -1, bestDp = INF;
        for (int i = 0; i <= canPassVertexesNum; i++){
            if (dp[n-1][hashDp(i,0)] < bestDp){
                bestDp = dp[n-1][hashDp(i,0)];
                besti = i;
            }
        }
        printAll(n-1,besti,0,0);
    }
    void printPassAllMustVertexesConstraints(){
        fprintf(fout,"**********Pass All Must Vertexes constraints**********\n");
        int mask = (1 << mustPassVertexesNum) - 1;
        int besti = -1, bestDp = INF;
        for (int i = 0; i <= bound; i++){
            if (dp[n-1][hashDp(i,mask)] < bestDp){
                bestDp = dp[n-1][hashDp(i,mask)];
                besti = i;
            }
        }
        printAll(n-1,besti,mask,0);
    }
    void printPassAllMustEdgesConstraints(){
        fprintf(fout,"**********Pass All Must Edges constraints**********\n");
        int mask = maxMask - ((1 << mustPassVertexesNum) - 1);
        int besti = -1, bestDp = INF;
        for (int i = 0; i <= bound; i++){
            if (dp[n-1][hashDp(i,mask)] < bestDp){
                bestDp = dp[n-1][hashDp(i,mask)];
                besti = i;
            }
        }
        printAll(n-1,besti,mask,0);
    }
    void printPassAllMustConstraints(){
        fprintf(fout,"**********Pass All Must constraints**********\n");
        int mask = maxMask;
        int besti = -1, bestDp = INF;
        for (int i = 0; i <= bound; i++){
            if (dp[n-1][hashDp(i,mask)] < bestDp){
                bestDp = dp[n-1][hashDp(i,mask)];
                besti = i;
            }
        }
        printAll(n-1,besti,mask,0);
    }
    void printWeightConstraints(){
        fprintf(fout,"**********Pass Weight constraints**********\n");
        for (int i = 0; i <= bound; i++){
            for (int mask = 0; mask <= maxMask; mask++)if (dp[n-1][hashDp(i,mask)] != INF){
                int a = 0, b = 0 ;
                for (int j = 0; j < mustPassVertexesNum; j++) if (mask>>j&1) a++;
                for (int j = mustPassVertexesNum; j < mustPassEdgesNum + mustPassVertexesNum; j++) if (mask>>j&1) b++;
                qz.setMNum(i,a,b,dp[n-1][hashDp(i,mask)]);
            }
        }
        int besti = -1, bestMask;double bestValue = INF;
        for (int i = 0; i <= bound; i++){
            for (int mask = 0; mask <= maxMask; mask++)if (dp[n-1][hashDp(i,mask)] != INF){
                int a = 0, b = 0 ;
                for (int j = 0; j < mustPassVertexesNum; j++) if (mask>>j&1) a++;
                for (int j = mustPassVertexesNum; j < mustPassEdgesNum + mustPassVertexesNum; j++) if (mask>>j&1) b++;

                if (besti == -1 || bestValue > qz.value(i,a,b,dp[n-1][hashDp(i,mask)])){
                        bestValue = qz.value(i,a,b,dp[n-1][hashDp(i,mask)]);
                        besti = i;
                        bestMask = mask;
                }
            }
        }
        if (besti == -1){
            fprintf(fout,"No ,path!\n");
        }else{
            printAll(n-1,besti,bestMask,0);
        }
    }
    void printResult(){
        memset(vis,0,sizeof vis);
        printPassAllMustConstraints();
        printNoConstraints();
        printOnlyPassNumConstraints();
        printPassAllMustEdgesConstraints();
        printPassAllMustVertexesConstraints();
        printWeightConstraints();

        fprintf(fout,"**********other reference paths*********\n");
        for (int i=0;i<=bound;i++) printAll(n-1,i,maxMask,1);
        for (int i=maxMask;i>=0;i--) printAll(n-1,bound,i,1);

        if (!ansCnt) fprintf(fout,"sorry,no answer!\n");
    }
};
int main()
{
    #ifdef TIME
    double st = clock();
    #endif // TIME

    init();

    #ifdef TIME
    double ed = clock();
    cout<<"init time="<<(ed-st)/CLOCKS_PER_SEC<<endl;
    st=ed;
    #endif

    if (mustPassEdgesNum + mustPassVertexesNum <= 12){
        maxMask = (1<<maskOrder.cnt)-1; bound = 0;
        vertexBound = min( max(canPassVertexesNum, INF/(maxMask+1)/m) ,(DPSEC-1)/(maxMask+1));//空间限制。
        //cout<<vertexBound<<endl;
        qz.setMNum();
        dijkstra();

        #ifdef TIME
        ed = clock();
        cout<<"dijkstra time = " << (ed-st)/CLOCKS_PER_SEC<<endl;
        st = ed;
        #endif

        PRINT print;
        bound = max(bound, vertexBound); bound--;print.printResult();

        #ifdef TIME
        ed = clock();
        cout<<"print time = " << (ed-st)/CLOCKS_PER_SEC<<endl;
        #endif
    }else {
        OtherSolver otherSolver;
        otherSolver.solve();

        #ifdef TIME
        ed = clock();
        fprintf(fout,"dijkstra time = %.4lf\n",(ed-st)/(double)CLOCKS_PER_SEC);
        st = ed;
        #endif
    }
    fclose(fout);
    return 0;
}
