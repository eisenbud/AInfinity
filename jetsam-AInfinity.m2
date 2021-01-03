-*
///
--given a resolution A of R over S, and G or M over S, form tensor products
--G_i**A_u**A_v**..**A_w. Reconstruct the label (i,{u,v..w})? We'd need to know the names of the components.

wrote "targets", symbolPairs, the latter giving the source,target of the maps defined from m^A and m^G.

///
LabeledModule = new Type of Module
print class LabeledModule
LabeledChainComplex = new Type of ChainComplex
LabeledComplex = new Type of Complex

labeledModule = method()
labeledModule(VisibleList,Module) := LabeledModule => (L,F) -> (
    F':=new LabeledModule from F;
    if not F'.?cache then F'.cache = new CacheTable;
    F'.cache.label = L;
    F'.cache.factors = {F'};--singleton means not a tensor product module
    F'.cache.components = {F'};
    F'.cache.indices = {L};
    F'.cache.indexComponents = new HashTable from {L=>0};
--    F'.cache.module = F;
    F'
    )
-*
module = method()
module LabeledModule := Module => M -> new Module from M

labeledModule(Module) := LabeledModule => F -> labeledModule({},F)

getLabel = method()
--getLabel LabeledModule := VisibleList => F -> F.cache.label
--getLabel LabeledComplex := VisibleList => F -> F.cache.label
--getLabel LabeledChainComplex := VisibleList => F -> F.cache.label
getLabel Thing := VisibleList => F -> if (F.?cache and F.cache.?label)
                    then F.cache.label else
		    error"Not a labeled object"

labeledComplex = method()
labeledComplex(VisibleList, Complex) := LabeledComplex => (L,C) -> (
    C' := new LabeledComplex from C;
    for i from min C to max C do if class C_i === labeledModule 
       then C'_i = C_i else 
       C'_i = labeledModule({},C_i);
    for i from 1+min C to max C list map(C'_(i-1),C'_i, matrix C.dd_i);
    C'.cache = new CacheTable;
    C'.cache.label = L;
    C'
)

labeledChainComplex = method()
labeledChainComplex(VisibleList, ChainComplex) := LabeledChainComplex => (L,C) -> (
    C' := new LabeledChainComplex from C;
    for i from min C to max C do if class C_i === labeledModule 
       then C'_i = C_i else 
       C'_i = labeledModule({},C_i);
    for i from 1+min C to max C list map(C'_(i-1),C'_i, matrix C.dd_i);
    C'.cache = new CacheTable;
    C'.cache.label = L;
    C'
)

tensor(LabeledModule, LabeledModule) := LabeledModule => o -> (F,G) -> (
    ans := new LabeledModule from (module F ** module G);
    ans.cache.module = (module F ** module G);
    ans.cache.factors = {F,G};
    ans.cache.components = flatten apply(components F, M -> apply(components G, N -> 
	    module M ** module N));
    ans.cache.label = {getLabel F, getLabel G};
    ans)

LabeledModule**LabeledModule := (A,B) -> tensor(A,B)

directSum(LabeledModule, LabeledModule) := LabeledModule => (F,G) -> (
    F':= new LabeledModule from (module F ++ module G);
    F'.cache.label = {getLabel F,getLabel G};
    F'.cache.factors = {F'};--singleton means not a tensor product module
    F'.cache.components = {F,G};
    F'.cache.indices = {getLabel F,getLabel G};
    F'.cache.indexComponents = new HashTable from {getLabel F=>0,getLabel G => 1};
    F')

LabeledModule.directSum = (F,G)->(
    F':= new LabeledModule from (module F ++ module G);
    F'.cache.label = {getLabel F,getLabel G};
    F'.cache.factors = {F'};--singleton means not a tensor product module
    F'.cache.components = {F,G};
    F'.cache.indices = {getLabel F,getLabel G};
    F'.cache.indexComponents = new HashTable from {getLabel F=>0,getLabel G => 1};
    F')


--this doesn't work. Is it because 
--"directSum" has class "MethodFunctionSingle" instead of "MethodFunction"?

LabeledModule++LabeledModule := (A,B) -> directSum(A,B)
///
uninstallPackage "AInfinity"
restart
installPackage "AInfinity"
///
*-

-*
///
restart
debug loadPackage("AInfinity", Reload => true)

kk = ZZ/101
S = kk[a,b,c]

aSymbols(3,3,5)
aSymbols 5



km = coker vars S
k = labeledModule({}, coker vars S)
k1 = labeledModule({L1}, coker vars S)
k2 = labeledModule({L2}, coker vars S)
keys k1
getLabel k
getLabel k1
keys k.cache
k' = k++k
class k'
keys (k').cache


K = labeledChainComplex({KK}, koszul vars S)
getLabel K_1
getLabel K
class K_1
class module K_1
tensor(K_1, K_1)
class(K_1**K_1)
class(K_1 ++ K_1)
class directSum(K_1, K_1)
*-



tensorAssociativity (LabeledModule,LabeledModule,LabeledModule) := Matrix => (M0,M1,M2) ->(
    --produces the map from (M0**(M1**M2) to M0**M1**M2 = (M0**M1)**M2
    t := tensorAssociativity(M0,M1,M2);
    M := labeledModule(source t);
    M.cache.factors = {M_0, M_1**M_2};
    map(M0**M1**M2, M)
    )

reassociate1 = method()
reassociate1 (LabeledModule, ZZ,ZZ) := Matrix => (M,p) ->(
    M0 := ((M.cache.factors)_0).cache.factors_0;
    M1 := ((M.cache.factors)_0).cache.factors_1;
    M2 := (M.cache.factors)_1;
    t := tensorAssociativity(M0,M1,M2);
    N := target t;
    N.cache.factors = {M0,M1**M2};
    )


maps = method()
maps(Complex, ZZ) := HashTable => (Rres, bound) ->(
    --inductively construct the maps m_j on tensor products of degree d
    S := ring Rres;
    pdR := length Rres; 
    B := (complex apply(length Rres - 1, i -> -Rres.dd_(i+2)))[-2];

    frees := AFrees(Rres,bound);
    symbols := keys frees;
    m := new MutableHashTable;
    
    for d from 1 to bound do(
	for j from 1 to d do(
           ss := select(symbols, s -> sum s == d and length s == j); 
	    for s in ss do(
		for t in targets1(s,j) do
	        if j == 1 then (
		   if s_0 == 2 then m#(j,s) = 0 else  
		                    m#(j,s) = map(frees#t,frees#s, B.dd_(s_0)));
		if j == 2 then (
                    A0 := (complex S^1)[-2];
		    d1 := map(A0,B, i -> if (i == 2) then Rres.dd_1 else 0);
		    m2 := nullHomotopy (d1 ** id_B - id_B ** d1);
		    indices(source m2_5);
		    error();
		    	    ))));
    hashTable pairs m)
--	<<(d,j)<<ss<<endl;


tensorList = method()
tensorList List := Module => L -> (
    --tensor product of a list of modules
    if not class L_0 =!= Module then error "Input should be a list of Modules.";
    S := ring L_0;
    if #L == 0 then return S^1;
    if #L == 1 then return L_0;
    if #L > 1  then return tensorList(drop(L, -1)) ** last L)
    
symbolPairs = method()
symbolPairs (ZZ,ZZ,ZZ,ZZ) := List => (pdR, pdM, n, j) -> (
    --list of lists {p,q,s,t} such that s = (u,i), t = (v,j) are symbols; degree s = n, degree t = n-1; 
    --and s,t are equal in the places <p and >q, and q-p+1 = j.
    for s in bSymbols(pdR, pdM, n) list targets(s,j)/(t -> {s,t}))



///
bSymbols(3,3,7)
targets({2,4,0},2)
targets({2,0},2)
symbolPairs(3,3,5,2)
///

eagonSymbols = method()
eagonSymbols(ZZ,ZZ) := List => (n,i) ->(
    --symbol of the module Y^n_i, as a list of pairs, defined inductively from n-1,i+1 and n-1,0
    --assumes large number of vars and pd.
    if n === 0 then return {(i,{})};
    if i === 0 then return eagonSymbols(n-1,1);
    e' := eagonSymbols (n-1,0);
    e'1 := apply (e', L -> L_1|{i});
    eagonSymbols(n-1,i+1)|apply (#e', j-> (e'_j_0,e'1_j))
    )
 -*

bSymbols ZZ := List => n -> (
    --these are indexed with the module resolution component last, 
    --and the ring resolution component indexed as in the B complex: A_i = B_(i+1) for i>= 1.
    --note that the symbol is now a single list
    L :=eagonSymbols(n,0);
    apply(L, ell -> toList flatten(ell_1/(i->i+1), ell_0))
)

    if n === 0 then return {0};
    bS' := bSymbols n-1;
    apply(bS', s -> toList flatten

	)

bSymbols(ZZ,ZZ,ZZ) := List => (pdA,pdM,n) -> (
    L := bSymbols n;
    select(L, ell -> (
	    ell' := drop(ell, -1);
	    all(ell', u -> u <= pdA+1) and last ell <= pdM))
    )
*-
	  


tensorWithComponents = method()
tensorWithComponents(Module, Module, Function) := Module => (F, G, combineIndices) -> (
    if F == 0 or G == 0 then return (ring F)^0;
    (compsF, indicesF) := componentsAndIndices F;
    (compsG, indicesG) := componentsAndIndices G;
    comps := flatten for f from 0 to #compsF-1 list (
        for g from 0 to #compsG-1 list (
            newindex := if indicesF#f === null or indicesG#g === null
	       then null else combineIndices(indicesF#f, indicesG#g);
            newindex => directSum(1:(newindex=>(compsF#f ** compsG#g)))
            )
        );
    if #comps == 0 then (ring F)^0 else directSum comps
    )

tensorWithComponents(Module, Module) := Module => (F, G) -> tensorWithComponents(F, G, (a,b) -> a|b)
tensorWithComponents(Matrix, Module, Function) := Matrix => (phi, G, combineIndices) -> (
                          src :=  tensorWithComponents(source phi, G, combineIndices);
                          tar :=  tensorWithComponents(target phi, G, combineIndices);			  
			  map(tar,src,phi**G))

eTensor = method()
eTensor(Module,Module) := Module => (F, G) -> tensorWithComponents(F, G, (a,b) ->(a#0+b#0,a#1|b#1))
eTensor(Matrix,Module) := Matrix => (phi,G) -> tensorWithComponents(phi, G, (a,b) ->(a#0+b#0,a#1|b#1))

eTensor(ChainComplex, ChainComplex) := ChainComplex => (A,B) -> ( --TODO
  C0 := A**B;
  C := chainComplex( for i from 1+min C0 to max C0 list 
	      map(directSum(for j from min A to i list A_j**B_(i-1-j)),
		  directSum(for j from min A to i list A_j**B_(i-j)),
    	          matrix(C0.dd_i)));
  C[-min C0])

eTensor(ChainComplex, ChainComplexMap) := (G,d) -> 
    map(eTensor(G,target d), eTensor (G, source d), i-> eTensor(id_(G_i), d_i))
     
	      
eTensor(Ring, List) := (R,L) -> (
    --note that A**B**C**..**D = (((A**B)**C)**..**D) = tensor(R,{A..d}).
    --The order matters for chain complexes; maybe not for modules.
    if L === {} then return R^1;
    if #L === 1 then return L_0;
    eTensor(R,drop(L,-1))**last L
    )

labeledProducts = method()
labeledProducts(ChainComplex, ChainComplex, ZZ) := Sequence => (A,G,n) ->(
-*    returns a pair of lists of lengths n,n+1; the first element is a list
    {A,A**A,..,(A**..**A)}; the second is a list
    {G, A**G, A**A**G..} with <= n factors, where each
    component of each product is is labeled:
    {j_1..j_s} => A_(j_1)**..**A_(j_s)  while
    (i,{j_1..j_s}) => G_i**A_(j_1)**..**A_(j_s) 
*-
    AA := apply(n, i-> eTensor(ring A, toList(i+1:A)));
    GA := apply(n+1, i-> eTensor(ring A, {G}|toList(i:A)));
    (AA,GA)
    )
    

///
restart
needsPackage "Complexes"
debug loadPackage("AInfinity",Reload => true)
S = ZZ/101[x,y,z]
R = S/(ideal gens S)^2
M = coker vars R
mR = aInfinity(R,3);
pairs mR
mM = aInfinity(mR,M,3);
pairs mM
componentsAndIndices source mR#{1,3}
componentsAndIndices target mM#{3,4}
///


restart
needsPackage "Complexes"
--loadPackage("AInfinity", Reload =>true)
uninstallPackage "AInfinity"
restart
installPackage "AInfinity"

uninstallPackage "Complexes"
restart
installPackage "Complexes"
viewHelp Complexes

t = tensorAssociativity(B_2, B_2, B_2);
b = betti B
b ** b
(b ** b) ** b  ==
((b ** b) ** b ) ** b


------tensor associativity

for resolutions A of R, G of M, both length 3 , there is one nonzero component of m_3:
mM_3: B_2**B_2**G_0 ->G_3 == -mM_2(mB_2(B_2,B_2),G_0)-mM_2(B_2, mM_2(B_2,G_0))


1(2(3))->(1,2)3
1(2(3(4))) -> 1(2,3)4->(1,2)3)4
1(2(3

--why doesn't this work??

tensor List := Module => mods -> (
    if #mods == 1 then return mods_0;
    if #mods == 2 then return tensor(mods_0,mods_1);
    mods' := drop(mods,1);
    tensor(mods_0,tensor mods')
    )
mods = {S^2,S^3,S^4}
mods = {S^2,S^3}
tensor mods
tensor{S^2}

associativity = method()
associativity(List, List) := Matrix => blocks, mods -> (
-*
    blocks = {a,b,..,c} positive integers, 
    mods = {A_1,..,C_c}
    returns the map
    (A_1**..**A_a)**(B_1**..**B_b)**..**(C_1**..**C_c) -> A_1**..**C_c.
    Note that the built-in tensor product of multiple factors
    goes from left to right:
    tensorAssociativity: A*(B*C) -> A*B*C = (A*B)*C; 
*- 
    n := sum blocks;
   if blocks == {n-1,1} then tensorAssociativity(mods_0**;
   
viewHelp tensorAssociativity

S = ZZ/101[a,b,c]
G = res coker vars S
E = extend(G,schurComplex({2},G),id_(G_0))

components (source E)_2
code methods schurComplex
viewHelp SchurComplexes

-*
complex(for i from 1 to length G0 list 
	map(labeledModule((i-1,{}), G0_(i-1)),
	    labeledModule((i,{}), G0_(i)),
	    G0.dd_i));
*-
-*
--m#{3,4}
  sour := directSum components source m#{2,3};
  m#{2,3} = map(G_2, sour, matrix m#{2,3});
  toLift :=  map(G_2, B_2**B_2**G_0, 
  - m#{2,3}*(source m#{2,3})_[0]*mR#{2,4}**id_(G_0) --*t^-1 --mR#{2,-}(mR#{2,-}**1)
  - m#{2,3}*(source m#{2,3})_[1]*(id_(B_2)**m#{2,2}) --m(1**m#{2,-})
                 );
  m#{3,4} = toLift//m#{1,3};
hashTable pairs m)
*-

targets1 = method()
targets1 (VisibleList, ZZ) := List => (s,j) -> (
    --s is a bSymbol, j>=1.
    --output is a list of targets of maps collapsing j indices in the A-infinity structure on Rres
    len := #s;
    if j > len then return {} else
    if j == 1 then (
	L' := apply(len, i->apply(#s, k-> if k == i then s_k-1 else s_k));
    L := select(L', t -> all(len, i -> t_i >= 2));
	  ) else
    L = for i from 0 to len-j list 
      s_(toList(0..i-1))|{-1+sum(j, k -> s_(i+k))}|s_(toList(i+j..len-1));
    L
	 )

targets = method()
targets (VisibleList, ZZ) := List => (s,j) -> (
    --s is a bSymbol, j>=1.
    --output is a list of targets of maps collapsing j indices in the A-infinity structure on Rres**Mres
    len := #s;
    if j > len then return {} else
    if j == 1 then (
	L' := apply(len, i->apply(#s, k-> if k == i then s_k-1 else s_k));
    L := select(L', t -> all(len - 1, i -> t_i >= 2) and last t >= 0)
	  ) else
    L = for i from 0 to len-j list 
      s_(toList(0..i-1))|{-1+sum(j, k -> s_(i+k))}|s_(toList(i+j..len-1));
    L
	 )

--
A = freeResolution R1
freesA = AFrees(A,5)
X = freesA#{2}++freesA#{3,2}

indices((components X)_1)
indices X -- just the numbers
componentsAndIndices X -- gives the labels
G = freeResolution M
G2 = G**G
componentsAndIndices (G2_1)
frees = AFrees(A,G,4)
M = frees#{3,1}
M^[{3,1}]

picture id_(frees#{3,1})
displayBlocks id_(frees#{3,1})
indices (frees#{3,1})
components frees#{3,1}
componentsAndIndices frees#{3,1}
///
AFrees = method()
AFrees(Complex, ZZ) := HashTable => (Rres, bound) ->(
    -- A is a resolution of a ring R = S/I (as S-module S^1/I)
    -- returns a hash table of the labeled tensor products of free S-modules
    -- needed for forming the A-infinity structure on the resolution A
S := ring Rres;
B := (complex apply(length Rres - 1, i -> -Rres.dd_(i+2)))[-2];
frees := new MutableHashTable;
for n from 0 to bound do (
    bS := bSymbols(length Rres, n);
    apply(bS, s -> (
      frees#s = labeler(s,tensor(S,apply(#s, t->B_(s_t))))
	    )));
    hashTable pairs frees)

AFrees(Complex, Complex, ZZ) := HashTable => (Rres,Mres,bound) ->(
    -- A is a resolution of a ring R = S/I (as S-module S^1/I)
    -- G is a resolution of an R-module M (as S-module)
    -- returns a hash table of the labeled tensor products of free S-modules
    -- needed for forming the A-infinity structure on the two resolutions.
S := ring Rres;
B := (complex apply(length Rres - 1, i -> -Rres.dd_(i+2)))[-2];
frees := new MutableHashTable;
for n from 0 to bound do (
    bS := bSymbols(length Rres,length Mres, n);
    apply(bS, s -> (
      frees#s = labeler(s,tensor(S,apply(#s, t->(
			if t<#s-1 then B_(s_t) else Mres_(s_t)))));
	    )));
    hashTable pairs frees)

bSymbols = method()
bSymbols(ZZ,ZZ) := List => (pdR,d) ->(
--    lists of non-negative integers s_0..s_k that sum to d
--    such that 2 <= s_i <= maxA for all i
    lb := for k from 1 to d//2 list toList(k:2);
    C := for k from 1 to d//2 list compositions(k, d-2*k);
    B' := flatten apply(d//2, i -> C_i/(L-> L+lb_i));
    select(B', s -> all(#s, i-> s_i <= pdR+1))
    )

bSymbols(ZZ,ZZ,ZZ) := List => (pdR,pdM,d) ->(
--    lists of non-negative integers s_0..s_k that sum to d
--    such that 2 <= s_i <= maxA for i<k and 0<=s_k<=maxG.
    lb := apply(1+d//2, i-> toList(i:2)|{0});
    C := for k from 1 to d//2 + 1 list compositions(k, d-2*(k-1));
    B' := flatten apply(d//2+1, i -> C_i/(L-> L+lb_i));
    select(B', s -> all(#s-1, i-> s_i <= pdR+1) and s_(#s-1) <= pdM)
    )
///
restart
loadPackage"AInfinity"

S = ZZ/101[x,y]
K = complex koszul matrix{{x^2,y^3}}

K**K
(components (K**K**K)_3)_2
components oo

assert(K**K**K != K**(K**K))
assert(K**K**K == (K**K)**K)
assert (source tensorAssociativity(K,K,K) == K**(K**K))
assert (not source tensorAssociativity(K,K,K) == (K**K)**K)

apply(length (K**K**K), i->((K**K)**K).dd_(i+1) - (K**(K**K)).dd_(i+1))

t = (A,B,C) -> tensorAssociativity(A,B,C)
s = method()
s(Module, Module, Module) := Matrix => (A,B,C) -> (tensorAssociativity(A,B,C)^-1
s(ChainComplex, ChainComplex, ChainComplex) := ChainComplexMap => (A,B,C) -> (
    D := (A**B)**C;
    E := A**(B**C);
    ta := tensorAssociativity(A,B,C);
    map(D,E,for i from min D to max D do 
	for 
    C0 = A**B**C;
    C1 = A**(B**C);
    F0 := tensorAssociativity(A_0,B_0,C_0);
    extend(id_C0//F0, C1)

    
    

(K**K)**((K**K)**K) == (K**K)**(K**K**K)
(K**K)**((K**K)**K) != (K**K)**K**K**K
Goal = (K**(K**K)**K) 
G1 = (K**K)**(K**K) 
G1 == (K**K**(K**K))
G2 = K**(K**(K**K))
Start = (((K**K)**K)**K) 
target t(K**K,K,K) == Start
source t(K**K,K,K) == G1
target t(K,K,K**K) == G1
source t(K,K,K**K) == G2
target (id_K**s(K,K,K)) == G2

///


TEST///
S = ZZ/101[a,b]
A = koszul vars S
B = koszul matrix{{a^2,b^3}}
C = koszul matrix{{b^4,a^5}}
assert(A**B**C == tensor(S,{A,B,C}))
assert(tensor(S,{C,B,A}) != tensor(S,{A,B,C}))

(((A**B)**C)**D) <-(A**B)**(C**D)<-A*(B*(C**D)) <- A*((B*C)*D)
tensorAssociativity(A*B,C,D)
tensorAssociativity(A,B,C**D)
id_A**tensorAssociativity(B,C,D)

A1*A2*....*An -- (A1*..*Ap)*((Ap'*..Aq)*(Aq..An)) = (A1*..*Ap)*(Ap'*..Aq*Aq'*..*An)
///

tensorDegrees = method()
tensorDegrees List := List => L -> (
    --L is a list of lists of ZZ. If L_i is the list of degrees of
    --a free module F_i, where F is a list of free modules,
    --then the output is a list of the degrees
    --of the free module tensor F.
    n := #L;
    if n ==0 then return {0};
    if n == 1 then return L_0;
    M := tensorDegrees drop(L, 1);
    flatten apply(L_0, ell -> apply(M, m-> ell+m))
    )
