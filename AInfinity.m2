newPackage(
	"AInfinity",
    	Version => "0.1", 
    	Date => "October 4, 2020, rev December 2020",
        Authors => {{Name => "David Eisenbud", 
                  Email => "de@msri.org", 
                  HomePage => "http://www.msri.org/~de"},
	          {Name => "Mike Stillman", 
                  Email => "mike@math.cornell.edu", 
                  HomePage => "http://pi.math.cornell.edu/~mike"}},
	PackageExports => {"Complexes", "DGAlgebras"},
        Headline => "AInfinity structures on free resolutions",
        DebuggingMode => true
	)

export {
    "aInfinity",
    "burke",
    "golodBetti",
    "labeledTensorComplex",
    "labeledDirectSum",
    "mapComponents",
    "componentsAndIndices",
    "label",
    "picture",
    "displayBlocks",
    "extractBlocks"
    }

///
restart
uninstallPackage "AInfinity"
restart
installPackage "AInfinity"
check AInfinity
restart
debug loadPackage "AInfinity"
///

burke = method()
burke(Ring, Module, ZZ) := Complex => (R,M,len) ->(
    --put the map components together into what should be a complex.
    mA := aInfinity R;
    mG := aInfinity(mA,M);
    D := mapComponents(mA,mG,len);
    labeledTensorComplex(R,complex(D/sum))
    )

burkeData = method()
burkeData(Module,ZZ) := List => (M,n) ->(
--currently (11/26) 
--F = burkeData(M,n) 
--produces the list of the free modules indexed 0..n in the Burke resolution,
--in a form that things like F_5^[{3,2,0}] work (this is the projection).
--output is a list of labeled S-modules, where 
--S = ring presentation ring M.
R := ring M;
S := ring presentation R;
RS := map(R,S);
G := labeledTensorComplex freeResolution(pushForward(RS, M), LengthLimit=>n);
A' := freeResolution (coker presentation R, LengthLimit => n-1);
A'' := labeledTensorComplex(A'[-1]);
A := A''[1];
--B0 := labeledTensorComplex complex(apply(length A-1, i-> A.dd_(i+2)))[-2];
B0 := labeledTensorComplex complex(apply(length A-1, i-> -A.dd_(i+2)),Base =>2);
BB := {G}|apply(n//2, i->labeledTensorComplex(toList(i+1:B0)|{G}, LengthLimit => n));
C := apply(n+1, i-> select(apply(BB,b-> b_i), c -> c != 0));
apply(C, c -> labeledDirectSum c))

mapComponents = method()
mapComponents List := List => u -> (
    --u = {u_0..u_n}; for i<n, u_i represents a free module in B, the truncated, shifted res of R^1; 
    --u_n represents a free module in G, the S-resolution of the R-module M.
    --output is a list whose elements have the form 
    --{sign, p,q,{v_0..v_m}} corresponding to
    --a map with
    --target =  {v_0..v_m} = {u_0..u_(p-1), v_p, u_(q+1)..u_n}
    --that collapses
    --u_p..u_q to a single index v_p = -1+sum(for i from p to q list u_i), 
    --where sign is (-1)^sum(apply p, i->u_i).
    --We require also v_0..v_(m-1)>=2 and v_m>=0; otherwise this is not 
    --the index of a module in the resolution.

    sign := p-> (-1)^(sum apply(p, i->1+u_i)); --replaced u_i by 1+u_i 12/28
    n := #u-1;
    L0 := apply(n+1, p-> {sign p, p,p,u_{0..p-1}|{u_p-1}|u_{p+1..n}});
    L1 := flatten apply(n, p -> for q from p+1 to n list {sign p, p,q,u_{0..p-1}|
	                         {-1+sum for i from p to q list u_i}|
		                 u_{q+1..n}});
    L := L0|L1;
    select(L, LL -> all (drop(LL_3,-1), p -> p >= 2) and last LL_3 >= 0)
    )

mapComponents(HashTable, HashTable, ZZ) := List =>(mA,mG,len) ->(
    --The output is a list D_1..D_len
    --where D_t is a list of  the matrices of maps 
    --F_t ->comp(u,F_t) -> comp(v, F_(t-1) -> F_(t-1)
    --where comp(u,F_t) is the component of F_t labeled u
    --and similarly for v,F_(t-1).
    --Thus sum D_t will be the map F.dd_t in the Burke resolution.
    R := mA#"ring";
    S := ring presentation R;
    B := mA#"resolution";
    M := mG#"module";
    G := mG#"resolution";
    F := burkeData(M,len); -- the list of labeled free modules

   --Now form the components of the maps. 

      for t from 1 to len list (
  
   --First construct vv, the list of valid maps F_t --> F_(t-1).
	c :=componentsAndIndices F_t;
	flatten apply(#c_0, s->(
	    u := c_1_s;
	--now focus on the maps starting from the u component of F_t
    	    numRComponents := #u-1;
    	    vv0 := mapComponents u; -- not all the vv0_i are valid.
	    (C,K) := componentsAndIndices F_(t-1);	    
	    vv := select(vv0, v-> member(v_3,K)); 
	  --for each member v of  vv, the list v_3 is the index of a component
	  --of F_(t-1) to which the u component maps.
	  --The rest of v describes the map, as follows:
    	    for v in vv list (
		sign := v_0;
		p := v_1;
		q := v_2;
		v_0*map(F_(t-1), F_t, 
		    (F_(t-1))_[u_{0..p-1}|{-1+sum u_{p..q}}|u_{q+1..numRComponents}]*
		    (if q<numRComponents 
		     then 
		        tensor (S, for i from 0 to p-1 list B_(u_i))**
	 		mA#(u_{p..q})**
	 		tensor(S, for i from q+1 to numRComponents-1 list B_(u_i))**
	 		G_(u_numRComponents)
                     else
	     		tensor(S, for i from 0 to p-1 list B_(u_i))**
	     		mG#(u_{p..q})
		    )*
		    (F_t)^[u])
             ))))
    )

--We should probably break this into pieces, and have a function that produces
--the individual component corresponding to a member v of vv.

///
restart
loadPackage("AInfinity", Reload => true)
check AInfinity
///

///
restart
loadPackage("AInfinity", Reload => true)
///
TEST///
kk = ZZ/101
S = kk[a,b,c,d]
R = S/(ideal(a,b,c,d))^2
mA = aInfinity R
K = koszul vars R
mG =apply(3,i-> aInfinity (mA,coker K.dd_(i+1)));
///

///
restart
loadPackage("AInfinity", Reload => true)
///
TEST///
S = ZZ/101[a..d]
R = S/ideal"a3,b3,c3,d3"
mA = aInfinity R;

--tensorCommutativity(M,N): M**N --> N**M.
B = mA#"resolution"
--m{2,2} is skew-symmetric, mimicking A_1**A_1 -> A_2
assert (0==mA#{2,2}+mA#{2,2}*tensorCommutativity (B_2,B_2)) -- anti-commutative
assert (0==mA#{3,3}-mA#{3,3}*tensorCommutativity (B_3,B_3)) -- commutative
assert (0==mA#{3,2}+mA#{2,3}*tensorCommutativity (B_3,B_2)) -- this seems wrong;I would have thought that 2,3 should commute.

///


///
restart
loadPackage( "AInfinity", Reload => true)
///




///
--Roos example: Claimed to be non-Golod with trivial homology algebra.
restart
debug needsPackage "AInfinity"
kk = ZZ/5
S = kk[x,y,z,u]
I = ideal(u^3, x*y^2, (x+y)*z^2, x^2*u+z*u^2, y*y*u+x*z*u, y^2*z+y*z^2) -- has the betti nums as in Roos
R = S/I
betti res coker presentation R

mA = aInfinity R
mG = aInfinity(mA,coker vars R, LengthLimit =>4) 
K = select(keys mA, k->class k_0 === ZZ)
netList apply(K, k -> picture mA#k)

elapsedTime F = burke(R,coker vars R,6)
picture F
F.dd^2==0 --bug! is back. OK mod 2
F.dd_5*F.dd_6 =!= 0
picture(F.dd_5*F.dd_6)
--problem is {2,2,2,0}->{4,0}

picture F.dd_6 
--{2,2,2,0} -> {5,0}++{2,3}++{3,2,0}++{2,3,0}++{2,2,1}
picture F.dd_5 
--{5,0}++{4,1}++{3,2,0}++{2,3,0} --> {4,0}
--So the possible compositions are

-- {2,2,2,0} -> {5,0} -> {4,0}
g1 = extractBlocks(F.dd_5,{4,0},{5,0})*extractBlocks(F.dd_6,{5,0},{2,2,2,0})
-- {2,2,2,0} -> {3,2,0} -> {4,0}
g2 = extractBlocks(F.dd_5,{4,0},{3,2,0})*extractBlocks(F.dd_6,{3,2,0},{2,2,2,0})
-- {2,2,2,0} -> {2,3,0} -> {4,0}
g3 = extractBlocks(F.dd_5,{4,0},{2,3,0})*extractBlocks(F.dd_6,{2,3,0},{2,2,2,0})

assert(g1+g2+g3 == extractBlocks(F.dd_5*F.dd_6, {4,0}, {2,2,2,0}))
assert(g1-g2-g3 == 0)
elapsedTime res(coker vars R, LengthLimit => 7)

testAInfinity mA

---

-- note: if we put a minus sign in front of dm where it probably should be,
-- the first two examples are still ok and this third one breaks at
-- F.dd_3*F.dd_4:

-- --problem is {2,2,0}->{2}

-- picture F.dd_4
-- --{2,2,0} -> {3}++{3,0}++{2,1}
-- picture F.dd_3
-- --{3}++{3,0}++{2,1} --> {2}
-- --So the possible compositions are

-- -- {2,2,0} -> {3} -> {2}
-- g1 = extractBlocks(F.dd_3,{2},{3})*extractBlocks(F.dd_4,{3},{2,2,0})
-- -- {2,2,0} -> {3,0} -> {2}
-- g2 = extractBlocks(F.dd_3,{2},{3,0})*extractBlocks(F.dd_4,{3,0},{2,2,0})
-- -- {2,2,0} -> {2,1} -> {2}
-- g3 = extractBlocks(F.dd_3,{2},{2,1})*extractBlocks(F.dd_4,{2,1},{2,2,0})

-- assert(g1+g2+g3 == extractBlocks(F.dd_3*F.dd_4, {2}, {2,2,0}))
-- g1+g2+g3
-- g1+g2-g3 
-- g1-g2+g3
-- g1-g2-g3

///

///
--3-variable bug!
restart
loadPackage( "AInfinity", Reload => true)
kk = ZZ/101
S = kk[a,b,c]
R = S/((ideal a^2)*ideal(a,b,c)) -- a simple 3 variable Golod ring
K = koszul vars R
M = coker K.dd_2

mA = aInfinity R
mG = aInfinity(mA,M)
isWellDefined D
source D
prune HH_3 BG
prune HH_3 B
pBG := hashTable(for i from lo to min(hi,max G) list i=>(BG_i)^[{2,i-2}])
hi
target (B_2**G, BG, pBG, Degree => -2)

nullHomotopyFreeSource D
nullHomotopyFreeSource = f -> (
    -- f:ComplexMap
    -- key assumption: 'source f' is a complex of free modules
    -- result is a ComplexMap h : C --> D, of degree degree(f)+1
    C = source f;
    D = target f;
    deg := degree f + 1;
    hs := new MutableHashTable;
    (lo,hi) := concentration f;
    for i from lo to hi do (
        if hs#?(i-1) then ( 
            rem := (f_i - hs#(i-1) * dd^C_i) % (dd^D_(i+deg));
            if rem != 0 then return null; -- error "can't construct homotopy";
            hs#i = (f_i - hs#(i-1) * dd^C_i) // (dd^D_(i+deg))
            )
        else (
            rem = f_i % dd^D_(i+deg);
            if rem != 0 then return null; -- error "can't construct homotopy";
            hs#i = f_i // dd^D_(i+deg)
            )
        );
    map(D, C, new HashTable from hs, Degree => deg)
    )


F = burke(R,M,5)
G = mG#"resolution"
assert(F.dd^2 == 0)
assert all(length F -1, i-> prune HH_(i+1)F == 0)
--find and squash!
picture(F.dd_4*F.dd_5)
-- --problems with {2,2,1}->{3}, {3,2,0} -> 3 and {2,3,0}->3
--try {3,2,0} first.
picture F.dd_5
{3,2,0} -> {4,0}++{3,1}++{2,2,0} -> {3}
mapComponents {3,2,0}

A = extractBlocks(F.dd_5, {{4,0},{3,1},{2,2,0}}, {{3,2,0}})
A1 = extractBlocks(F.dd_5, {{4,0}}, {{3,2,0}})
A2 = extractBlocks(F.dd_5, {{3,1}}, {{3,2,0}})
A3 = extractBlocks(F.dd_5, {{2,2,0}}, {{3,2,0}})

picture F.dd_4
B = extractBlocks(F.dd_4, {{3}}, {{4,0},{3,1},{2,2,0}})
B1 = extractBlocks(F.dd_4, {{3}}, {{4,0}})
B2 = extractBlocks(F.dd_4, {{3}}, {{3,1}})
B3 = extractBlocks(F.dd_4, {{3}}, {{2,2,0}})
C1 = B1*A1
C2 = B2*A2
C3 = B3*A3
C1+C2+C3  --== B*A
****C1-C2+C3 -- this is 0. Suggests that passing by 3 should have sign + instead of -
C1+C2-C3
C1-C2-C3
B = mA#"resolution"
G = mG#"resolution"
G.dd_3*mG#{2,2,0}+mG#{2,1}*(B_2**mG#{2,0})+mG#{3,0}*(mA#{2,2}**G_0)
mG#{2,2,0} == -(mG#{2,1}*(B_2**mG#{2,0})+mG#{3,0}*(mA#{2,2}**G_0))//G.dd_3
-(mG#{2,1}*(B_2**mG#{2,0})+mG#{3,0}*(mA#{2,2}**G_0)) % G.dd_3 -- this is nonzero!! and we never check...

-- --{2,2,1} -> {3}++{3,0}++{2,1}
-- picture F.dd_3
-- --{3}++{3,0}++{2,1} --> {2}
-- --So the possible compositions are

-- -- {2,2,0} -> {3} -> {2}
-- g1 = extractBlocks(F.dd_3,{2},{3})*extractBlocks(F.dd_4,{3},{2,2,0})
-- -- {2,2,0} -> {3,0} -> {2}
-- g2 = extractBlocks(F.dd_3,{2},{3,0})*extractBlocks(F.dd_4,{3,0},{2,2,0})
-- -- {2,2,0} -> {2,1} -> {2}
-- g3 = extractBlocks(F.dd_3,{2},{2,1})*extractBlocks(F.dd_4,{2,1},{2,2,0})

-- assert(g1+g2+g3 == extractBlocks(F.dd_3*F.dd_4, {2}, {2,2,0}))
-- g1+g2+g3
-- g1+g2-g3 
-- g1-g2+g3
-- g1-g2-g3

///

aInfinity = method(Options => {LengthLimit => null})
aInfinity Ring := HashTable => o -> R -> (
    --R should be a factor ring of a polynomial ring S
    --The HashTable returned contains the A-infinity structure on an
    --S-free resolution A of R up to m_n: B^(**n) --> B
    --CAVEAT: for the moment n = 3 is fixed! 
--old notation: m#{p,{u_1..u_p}}
--new notation: m#{u_1..u_p}. This is the map that has source
--B_(u_1)**..**B_(u_p), a p-factor tensor product.

m := new MutableHashTable;
m#"ring" = R;
S := ring presentation R;
RS := map(R,S);
A := freeResolution coker presentation R;
B := labeledTensorComplex complex(
           apply(length A-1, i -> 
	   map(A_(i+1), A_(i+2), -A.dd_(i+2))), 
	   Base =>2);
m#"resolution" = B;

limit := 1+max B;
if o.LengthLimit =!= null then limit = o.LengthLimit;

--m#{u_1}
mA := new MutableHashTable;
--apply(1+length B , i-> m#{i+2} = - A.dd_(i+1));
apply(1+length B , i-> m#{i+2} = B.dd_(i+2));

--error();
--m#{u_1,u_2}
B2 := labeledTensorComplex({B,B}, LengthLimit => limit);
A0 := complex {A_0};
d1 := map(A_0, B_2, A.dd_1); --the positive sign is a literal interpretation of Burke
d1d1 := hashTable for i from min B to max B2 -2 list 
       i+2 => (d1**id_(B_i))*(B2_(i+2))^[{2,i}] - (id_(B_i)**d1)*(B2_(i+2))^[{i,2}];
--D := map(A0**B,B2,d1d1, Degree => -2);
--error();

D := map(labeledTensorComplex{A0,B},B2,d1d1, Degree => -2);
D := map(A0**B,B2,d1d1, Degree => -2);
lo := hi:= null;
assert (isComplexMap D);
m0 := nullHomotopy D;
for i from 4 to 1+(concentration B)_1 do(
    (C,K) := componentsAndIndices B2_i;
    for k in K do (
	k' := {k_0+k_1-1};
	m#k = map(target (B_(i-1))^[k'], source (B2_i)_[k],
	       (B_(i-1))^[k']*m0_i*(B2_i)_[k]
	        )
	)
    );
--error();
--m#{u_1..u_3}	                    
B3 := labeledTensorComplex(toList(3:B),LengthLimit => limit);
e := apply(3, ell -> toList(ell:0)|{1}|toList(3-ell-1:0));

for i from 3*2 to min(limit, 1+max B) do(
        co := select(compositions(3,i,max B), c -> min c >= 2);	
	for k in co do(
	    dm3 := -(m#{sum k_{0,1}-1,k_2} * (m#(k_{0,1})**B_(k_2)) + 
	
	    (-1)^(k_0)* m#{k_0,sum k_{1,2}-1} * (B_(k_0)**m#(k_{1,2})) +
        
	    sum(apply(3, ell -> if min(k-e_ell) <= 1 then 0
	        else (mm := tensor(S, apply(3, i-> if i == ell then m#(k_{ell}) else B_(k_i)));
	        (-1)^(sum k_{0..ell-1})*m#(k-e_ell)*mm)))
                    );
	       --mm is m#(k_{ell}) tensored with factors B_(k_i) in the appropriate order. eg, 
	       --for example, if ell = 0,then
	       --mm = m#(k_{0})**B_(k_1)**B_(k_1)

    	test := dm3%B.dd_(i-1);
	if test != 0 then (
	    <<"i = "<<i<<" k = "<<k<<endl;
	    error"dm failed to lift in aInfinity(Ring)"
	    );

	m3 := dm3//B.dd_(i-1);
        m#k = map(B_(i-1), B3_i, m3*B3_i^[k])
	)
     );
hashTable pairs  m
)

aInfinity(HashTable, Module) := HashTable => o -> (mR, M) -> (
    --R = ring M should be a factor ring of a polynomial ring S
    --mR = aInfinity R an AInfinity structure on a resolution A of R
    --M an R-module
    --The HashTable returned contains the A-infinity structure on 
    --an S-free resolution of M up to stage n.
    --CAVEAT: for the moment n = 3, and we compute only
    --m#{u} for #u = 1,2,3
    
m := new MutableHashTable;
m#"module" = M;
B := mR#"resolution";
R := ring M;
S := ring presentation R;
A := labeledTensorComplex freeResolution coker presentation R;
RS := map(R,S);


Mres := freeResolution pushForward(RS,M);
G := complex labeledTensorComplex{Mres};
m#"resolution" = G;
limit := if o.LengthLimit =!= null then o.LengthLimit else 1+max G;

--m#u, #u=1
  apply(length G , i-> m#{i+1} = G.dd_(i+1));    

----m#u, #u=2
BG := labeledTensorComplex({B,G}, LengthLimit => limit);
A0 := complex {A_0};
d1 := map(A_0, B_2, A.dd_1); -- the positive sign should in any case be the same as in aInfinity Ring.
dG := hashTable for i from min G to min(limit-2, max G) list
              i+2 => (d1**id_(G_i))*(BG_(i+2))^[{2,i}];
D := map(A0**G, BG, dG, Degree => -2);
--lo :=null;hi := null;
(lo,hi) := concentration D;
for i from lo+1 to hi list
     ( 0 ==
	 (A0**G).dd_(i-2)*D_i - D_(i-1)*BG.dd_i
	 );

m0 := nullHomotopy D;

for i from 2 to min(limit, 1+(concentration G)_1) do( --was just 1+(concentration G)_1
    (C,K) := componentsAndIndices BG_i;
    for k in K do (
	k' := {k_0+k_1-1};
	m#k = map(G_(i-1), source (BG_i)_[k],m0_i*(BG_i)_[k])
	)
    );

--m#u, #u=3	                       );
B2G := labeledTensorComplex (toList(2:B)|{G}, LengthLimit => limit);
e := apply(3, ell -> toList(ell:0)|{1}|toList(3-ell-1:0));


for i from 4 to min(limit, 1+max G) do( -- 4 used to be min B2G, but we changed the def of B
	(C,K) := componentsAndIndices (B2G_i);
	for k in K do(
fac := null;
MM := hashTable apply(e, ee-> (
   	p := position(ee, j-> j==1);
	if not((p<2 and mR#?{k_p}) or (p == 2 and m#?{k_p})) 
	   then ee => S^0 
           else ee => tensor(S, 
				 apply(3, j -> (
				   if j<2 then 
				       (if ee_j == 0 then fac = B_(k_j) else fac = mR#{k_j});
		                   if j == 2 then(if ee_j == 0 then fac = G_(k_j) else fac = m#{k_j});
				      fac)
				  ))));
		      
	dm3 := -( m#{sum k_{0,1}-1,k_2} * (mR#(k_{0,1})**G_(k_2)) +
	
	       (-1)^(1+k_0) * m#{k_0,sum k_{1,2}-1} * (B_(k_0)**m#(k_{1,2})) +
	       --sign changed 12/28        
	       
	       sum(apply(#e, ell ->
			if min(k-e_ell-{2,2,0})<0 then 0 else 
		       (-1)^(sum k_{0..ell-1}) * m#(k-e_ell) * MM#(e_ell)))
		   );

    	test := dm3%G.dd_(i-1);
	if test != 0 then (
	    <<"i = "<<i<<" k = "<<k<<endl;
	    error"dm failed to lift in aInfinity(Module)"
	    );

	m3 := dm3//G.dd_(i-1);

        m#k = map(G_(i-1), source ((B2G_i)_[k]), m3))
     );
hashTable pairs  m)


///
restart
debug loadPackage("AInfinity", Reload => true)
needsPackage "DGAlgebras"
kk = ZZ/101
S = kk[a,b,c]
R = S/((ideal a^2)*ideal(a,b,c))
mA = aInfinity R

assert isGolod R
M = coker vars R
E = burke(R,M,5)
E.dd^2 -- F_5-> F_4->F_3 is not 0. However, F_4 -> F_3 does surject onto ker F_3->F_2,
picture (E.dd_4 * E.dd_5)
picture E.dd_5
picture E.dd_4
extractBlocks(E.dd_4,{3,0},{4,0})*extractBlocks(E.dd_5,{4,0},{3,2,0})+
extractBlocks(E.dd_4,{3,0},{2,2,0})*extractBlocks(E.dd_5,{2,2,0},{3,2,0})

mA = aInfinity R
B = mA#"resolution"
A = freeResolution coker presentation R
B.dd
A.dd
A2=labeledTensorComplex{A,A}
B2=labeledTensorComplex{B,B}-- first half the same, not second!
B2' = dual B2
A2' = dual A2[2]
phi0' = map(A2'_(-8),B2'_(-8),1)
phi' = extend(A2',B2',phi0')
phi = dual phi'
P = map(B2,A2[-2],phi)

mul0= map(A_0,A2_0,1)
mul = extend(A,A2, mul0)

(C,K) = componentsAndIndices B2_5
(CA,KA) = componentsAndIndices A2_3
k = K_0
k' = apply(k, i->i-1)
A2_3_[k']

B2_5^[k]
ring A===ring B
phi = hashTable(apply(length A, i-> i=>if i >0 then map(A_i,B_(i+1),1) else map(A_0,B_0,0)))

///


///
restart
debug loadPackage("AInfinity")
needsPackage "CompleteIntersectionResolutions"
S = ZZ/101[a,b,c]
R = S/ideal"a3,b3,c3"
M = coker vars R
mA = aInfinity R
mG = aInfinity (mA,M) 
A = res coker presentation R
G = res pushForward((map(R,S)),M)
AG = A**G
m0 = map(G_0, AG_0, 1)
mm = extend(G,AG,m0)
indices G
m2 = mm_2*(AG_2)_[(1,1)]
mG = new MutableHashTable from mG
mG#{2,{2,1}}
mG#{2,{2,1}} = m2
mG = hashTable pairs mG

/// 



///
restart
loadPackage("AInfinity", Reload => true)
kk = ZZ/101
S = kk[a,b,c]
R = S/((ideal a^2)*ideal(a,b,c)) -- a simple 3 variable Golod ring
K = koszul vars R
M = coker K.dd_2

mA = aInfinity R
B = mA#"resolution"
mG = aInfinity(mA,M)
G = mG#"resolution"

keys mG
mG#{2,2,0}
m#{sum k_{0,1}-1,k_2} * (mR#(k_{0,1})**G_(k_2)) +
1^(k_0) * m#{k_0,sum k_{1,2}-1} * (B_(k_0)**m#(k_{1,2})) 
m#{3,0}*(mR#{2,2}**G_0)

m#{2,1}*(B_2**m#{2,0})
m3 = dm3//G.dd_3
///


///
restart
debug loadPackage("AInfinity")
needsPackage "Complexes"
kk = ZZ/101
S = kk[x_1..x_3]
R = S/(x_1*ideal vars S)
R = S/((ideal vars S)^3)
R = S/ideal apply(gens S, x -> x^3)
RS = map(R,S)
M = coker vars R
elapsedTime mR = aInfinity R

G = (freeResolution pushForward(RS,M))
B = mR#"resolution"
BG = labeledTensorComplex{B,G}
p = new MutableHashTable from
for i from 2 to length G list i=>(presentation R ** G_(i-2))*(BG_i)^[{2,i-2}]
p#2
p#3
nullHomotopy map(G[-2],BG,p)
G[-2]
BG

for i from 2 to 4 list betti((G[-2])_i**presentation R)
map(G[-2],BG,i-> if G_i != 0 then (G[-2])_i**presentation R*(BG_i)^[{i,0}] else 0)
netList for i from 2 to 4 list (presentation R)*(BG_i)^[{2,i-2}]
for i from 0 to 3 list
((presentation R),(BG_(i+2))^[{2,i}])

componentsAndIndices (BG_i)
G

(G[-2])_i
(G[-2])_i**(presentation R * (BG_i)^[{i,0}])

componentsAndIndices(BG_i)
G0 = chainComplex complex G_0
BG0 = chainComplex labeledTensorComplex{B,G0}


concentration BG0
d = map(BG0, chainComplex BG, i-> if i<= 4 then ((BG_i)^[{i,0}])**presentation R else 0)
for i from 2 to 4 list betti( (BG_i)^[{i,0}]**presentation R)

(d_2//BG0.dd_3)*BG0.dd_3
m2 := map(S^1**G0, BG, i-> if i == 2 then presentation R ** G_0 else 0);

BG' := complex(for i from 2+min AG to max AG list AG.dd_i, Base => 2);
G' := complex(for i from 2 to max G list G.dd_i, Base => 1);
m0 := extend(G,AG,id_(G_0));
maps := hashTable for i from min G' to max G' list i+1=>map(G_i, BG'_(i+1), m0_i);





elapsedTime m = aInfinity (mR,M);
K = sort select(keys m, k->class k === List)
for k in K do <<k<<" "<< picture(m#k)<< betti m#k <<endl;

MS = pushForward(map(R,S), M)
G = res MS
A = res coker presentation R

///


///
restart
debug loadPackage("AInfinity")
needsPackage "Complexes"
kk = ZZ/101
S = kk[x_1..x_4]
R = S/(ideal vars S)^2
H = aInfinity R;
K = sort select(keys H, k->class k === List)
for k in K do <<k<<" "<< picture(H#k)<< betti H#k <<endl;

--note that m{3,{2,2,2}} = 0, since K res R^1 is a DG algebra!
///

testAInfinity = method()
testAInfinity HashTable := Boolean => mA -> (
--    Tests whether the pairs in mA define an AInfinity algebra structure
--    on the resolution of a ring R
frees := select(keys mA, k->class k_0 === ZZ);
n := max apply(frees, k-> #k);
B := mA#"resolution";
R := mA#"ring";
S := ring presentation R;

--m_1
if n >= 1 then(
    lenRes := (max select(frees, k-> #k ==1))_0 - 1;
    A := complex apply(lenRes, j -> mA#{j+2});
    t := all(lenRes, j -> prune HH_(j+2) A == 0);
    if not t then (<<"mA_1 failed."<<endl; return false)
    );

--m_2
if n >= 2 then (
    B2 := labeledTensorComplex{B,B};
    A0 := complex {A_0};
    d1 := map(A_0, B_2, A.dd_1);
    d1d1 := hashTable for i from min B to max B list 
       i+2 => (d1**id_(B_i))*(B2_(i+2))^[{2,i}] - (id_(B_i)**d1)*(B2_(i+2))^[{i,2}];
    D := map(A0**B,B2,d1d1, Degree => -2);
    m0 := nullHomotopy D;

    tlist := flatten for i from 4 to 1+(concentration B)_1 list(
        (C,K) := componentsAndIndices B2_i;
        for k in K list (
	    k' := {k_0+k_1-1};
	    mA#k == - map(target (B_(i-1))^[k'], source (B2_i)_[k],
	        (B_(i-1))^[k']*m0_i*(B2_i)_[k]
	    )
	)
    );
    t = all(tlist, s->s);
    if not t then (<<"mA_2 failed."<<endl; return false)
))

 

///
restart
debug loadPackage "AInfinity"
check "AInfinity"
///


///
S = ZZ/101[a..d]
R = S/(ideal gens S)^ 2
elapsedTime mA = aInfinity R;
testAInfinity mA
///


///
restart
debug loadPackage("AInfinity", Reload => true)
kk = ZZ/101
S = kk[a,b,c]
R = S/ideal"a2-bc,b2,c2,ab,ac"
H = aInfinity R;
K = sort select(keys H, k->class k === List)
for k in K do <<k<<" "<< picture(H#k)<< betti H#k <<endl;
H#{2,{2,3}}
H#{2,{3,2}}
///

picture = method()
picture Matrix := (M1) -> (
    M := flattenBlocks M1;
    src := indices source M;
    tar := indices target M;
    netList (prepend(
        prepend("", src),
        for t in tar list prepend(t, for s in src list (
                mts := M^[t]_[s];
		cont := ideal M^[t]_[s];
                h := if mts == 0 then "." else if (numrows mts == numcols mts and mts == 1) then "id" else 
		if cont == ideal(1_(ring mts)) then "u" else "*"
                ))
        ), Alignment=>Center)
    )
picture Module := M -> picture id_M
picture Complex := C -> netList apply(toList(min C+1..max C), i-> picture C.dd_i)
picture ChainComplex := C -> netList apply(toList(min C+1..max C), i-> picture C.dd_i)

flattenBlocks = method()
flattenBlocks Module := (F) -> (
    if not isFreeModule F then error "expected a free module";
    (comps, inds) := componentsAndIndices F;
    compsLabelled := for i from 0 to #comps-1 list (
        inds#i => comps#i
        );
    directSum compsLabelled
    )

flattenBlocks Matrix := (M) -> (
    F := flattenBlocks target M;
    G := flattenBlocks source M;
    map(F,G,matrix M)
    )

displayBlocks = method()
displayBlocks Matrix := (M1) -> (
    M := flattenBlocks M1;
    src := select(indices source M, i-> i =!= null);
    tar := select(indices target M, i-> i =!= null);
    netList (prepend(
        prepend("", src),
        for t in tar list prepend(t, for s in src list (
                mts := M^[t]_[s];
                h := if mts == 0 then "." else if (numrows mts == numcols mts and mts == 1) then "1" else net mts
                ))
        ), Alignment=>Center)
    )

extractBlocks = method()
extractBlocks(Matrix, List) := Matrix => (phi, src) ->(
    -- returns the submatrix corresponding to the block or blocks listed in src.
    -- src is a list of integers or a list of such lists,
    -- respresenting block(s) in source phi.
    -- note that this behavior is DIFFERENT than the function with the same
    -- name in EagonResolution, where the list is an ordinal list of integers
    -- representing the blocks (in some order??).
    if class src_0 === ZZ then 
       srcList := {src} else srcList = src;
    phi1 := flattenBlocks phi;
    matrix {apply(srcList,Ls->
               phi1_[Ls])
	   }
    )


extractBlocks(Matrix, List, List) := Matrix => (phi, tar, src) ->(
    -- returns the submatrix corresponding to the block or blocks listed in src and tar.
    -- src and tar are lists of integers or lists of such lists,
    -- respresenting block(s) in phi.
    -- note that this behavior is DIFFERENT than the function with the same
    -- name in EagonResolution, where the list is an ordinal list of integers
    -- representing the blocks (in some order??).
    if class src_0 === ZZ then 
       srcList := {src} else srcList = src;
    if class tar_0 === ZZ then
       tarList := {tar} else tarList = tar;
    phi1 := flattenBlocks phi;
    matrix apply(tarList, Lt -> apply(srcList,Ls->
               phi1_[Ls]^[Lt])
	   )
    )
    
///
restart
loadPackage("AInfinity", Reload => true)
kk = ZZ/5
S = kk[a,b,c]
R = S/((ideal a^2)*ideal(a,b,c)) -- a simple 3 variable Golod ring
K = koszul vars R
M = coker K.dd_3
E = burke(R,M,5)
E.dd^2
apply(length E, i-> prune HH_(i)E)
E.dd_2
picture E.dd_2
displayBlocks E.dd_2
extractBlocks(E.dd_2,{1},{2,0})
picture extractBlocks(E.dd_2,{1},{{2},{2,0}})


displayBlocks E.dd_4
betti E.dd_4
///

labels := method()
labels Module := List => M -> (
    if M.cache#?"label" then M.cache#"label" else
      if M.cache.?components then (
	L := M.cache.components;
	if not (L_0).cache#?"label" then error"no labels" else
	  apply(M.cache.components, N ->  N.cache#"label"))
    )

compositions(ZZ,ZZ,ZZ) := (nparts, k, maxelem) -> (
    -- nparts is the number of terms
    -- k is the sum of the elements
    -- each element is between 0 <= maxelem.
     compositionn := (n,k) -> (
	  if n===0 or k < 0 then {}
	  else if k===0 then {toList(n:0)}
	  else (
          set1 := apply(compositionn(n-1,k), s -> s | {0});
          set2 := apply(compositionn(n,k-1), s -> s + (toList(n-1:0) | {1}));
          set2 = select(set2, s -> s#(n-1) <= maxelem);
          join(set1, set2)
          )
      );
     compositionn = memoize compositionn;
     result := compositionn(nparts,k);
     compositionn = null;
     result
     );



tensor(Ring, List) := o -> (R,L) -> (
    --note that A**B**C**..**D = (((A**B)**C)**..**D) = tensor(R,{A..D}).
    --The order matters for chain complexes; maybe not for modules.
    --
    if L === {} then return R^1;
    if #L === 1 then return L_0;
    ans1 := tensor(R,drop(L,-1));
    ans1**last L
    )


componentsAndIndices = (F) -> (
    if not F.cache.?components then (
        -- F has no components
        ({F}, {null})
        )
    else if #F.cache.components == 1 then (
        if F.cache.?indices then 
            ({F}, F.cache.indices)
        else 
            ({F}, {null})
        )
    else (
        a := for f in F.cache.components list componentsAndIndices f;
        (flatten(a/first), flatten(a/last))
        )
    )



///
restart
debug loadPackage "AInfinity"
V = ZZ/101[x_1..x_3]
R = V/(ideal vars V)^3
R1 = V^1/(ideal vars V)^3
M = R**coker vars V
golodRanks(M,6)
betti res (M, LengthLimit =>6)
F = res M
N = coker F.dd_2
golodRanks(coker (F.dd_2),6)
res (N, LengthLimit =>6)
 ///    

golodRanks = method()
golodRanks (Module,ZZ) := List => (M,b) ->(
    --M is a module over a factor ring R = S/I, S a polynomial ring.
    --implements the rational function as power series. 
    --See Avramov, six lectures, p.50.
    --Output is the sequence of ranks, equal to those in the free resolution
    --if and only if M is a Golod module.
    expand := (nu,de,n) -> nu*sum(apply(n, i-> (de)^i)); --nu/(1-de) as power series
    R := ring M;
    p := presentation R;
    S := ring p;
    RS := map(R,S);
    MS := prune pushForward(RS,M);
    G := res MS;
    A := res coker p;
    x := symbol x;
    U := QQ[x];
    g := sum(1+length G, i-> x^i*rank G_i);
    a := sum(toList(1..length A), i-> x^(i+1)*rank A_i);
    c := (coefficients expand(g,a,b))_1;
    (reverse flatten entries c)_(toList(0..b))
    )

labeler = method()
--only direct sum modules can be labeled
labeler(Thing,Module) := (L,F) -> directSum(1:(L=>F));
--note that in labeling a direct sum, the labels must be applied to the modules
--And when the direct sum is formed.

label = method()
label(Module) := Thing => M-> (indices M)_0
label(List) := List => L-> apply(L, M ->(indices M)_0)

labeledDirectSum = method()
labeledDirectSum List := Module => L ->(
    --L is a list of labeled modules.
    ciL := apply(L, M -> componentsAndIndices M);
    directSum flatten apply(ciL, ci -> apply(#ci_0, i->(ci_1_i => ci_0_i)))
    )

labeledTensorComplex = method(Options => {LengthLimit => null})
labeledTensorComplex List := Complex => o -> L -> (
    --Input is L = {C_0..C_(p-1)}, a list of Complexes. 
    --Returns the tensor product D of the C_i. If LengthLimit => N is given, then
    --the result is computed only up to homological degree N.
    --Each term is labeled, so that the tensor product of {(C_i)_(u_i)} is labeled u = {..u_i..}
    --ComponentsAndIndices applied to D_i gives the correct list of indices, and
    --thus picture D works; but ALSO D_i_[u] and D_i^[u] return the inclusion
    --and projection correctly. (Note that this requires "double" labeling.)
    
    if class L_0 =!= Complex then error"Input should be a list of Complexes.";
    S := ring L_0;
    if #L == 1 and class L_0 === Complex then (
	B := L_0;
	F := for i from min B to max B list labeler({i}, B_i);
	return complex(for i from min B to max B -1 list 
	        map(F_(i-min B),F_(i+1-min B), B.dd_(i+1)),
		Base => min B)
        );
    p := #L;
    Min := apply(L, C->min C);
    Max := apply(L, C->max C);
    limit := if o.LengthLimit =!= null then o.LengthLimit else sum Max;
    modules := apply(#L + limit -1 - sum Min, i ->(
	    d := i+sum Min;
	    com := select(compositions(p,d), c -> 
		    all(p, i-> Min_i <= c_i and c_i <= min(limit, Max_i)) and c != {});
	    apply(com, co -> 
		    (co => labeler(co, 
			       tensor(S,apply(p, pp->(L_pp)_(co_pp))))))
	));
--note the (necessary) double labeling.
    modules = select(modules, tt-> #tt != 0);

suitable := v-> if min v == 0 then position (v, vv -> vv == 1) else null;
     -- v is a list of ZZ. returns null unless v has the form
     -- {0...0,1,0..0}, in which case it returns the position of the 1.
    
    if #modules == 1 then return complex({map(S^0,directSum(1:(modules_0_0)),0)}, Base => sum Min -1);
    
    d := for i from 0 to #modules -2 list(	
        map(directSum modules#i,
            directSum modules#(i+1),
            matrix table( -- form a block matrix
                modules#i, -- rows of the table
                modules#(i+1), -- cols of the table
                (j,k) -> ( -- j,k each have the form (List => Module)
		    indtar := j#0;
		    indsrc := k#0;		    
                    tar := j#1;
                    src := k#1;
		    p := suitable(indsrc - indtar);
                    m := map(tar, src, 
			if p === null then 0 
			else(
			    sign := (-1)^(sum(indsrc_(toList(0..p))));
			    print(i,j,k,p,sign);
			    phi := sign*(
			    (tensor(S, apply(p, q -> L_q_(indtar_q))))
			    **
			    (L_p).dd_(indsrc_p)
			    **
                            tensor(S, apply(#L-p-1, q -> L_(p+q+1)_(indtar_(p+q+1)))))
			))
		    ))));
     (complex(d,Base => sum Min))
     )
	       
labeledTensorComplex Complex := Complex => o-> C -> labeledTensorComplex{C}

labeledTensorComplex(Ring, Complex) := Complex => o -> (R,C)->(
    --preserve the labels on C while tensoring each free module with R.
    --NOTE that C must be a labeled complex!
    
    c := for i from min C to max C list componentsAndIndices C_i;
    if c_(min C)_1_0 === null then error"Input Complex must be labeled";
    D := for j from 0 to max C - min C list if #c_j_0 === 1 then 
    --this is to fix the directSum bug
        labeler(c_j_1_0, R**c_j_0_0) else
    	directSum apply(#c_j_0, i -> labeler(c_j_1_i, R**c_j_0_i));
    complex (for i from 1 to max C - min C list map(D_(i-1),D_i,R**C.dd_(i+min C)), Base => min C)
    )

///
restart
loadPackage"AInfinity"
S = ZZ/101[a,b,c]
R = S/((ideal vars S)^2)
maplist = apply(#gens R, i -> map(R^{-i},R^{-i-1},matrix{{R_i}}))
F = labeledTensorComplex(complex maplist)
picture F
FF = labeledTensorComplex {F,F}
FF.dd^2
FF.dd_3
F.dd_4
extractBlocks(FF.dd_3,{{1,1}},{{2,1}})
extractBlocks(FF.dd_3,{{1,1}},{{1,2}})

FF = labeledTensorComplex {B,B}
FF.dd^2
FF.dd_5

X = extractBlocks(FF.dd_5,{{2,2}},{{3,2}})
Y = extractBlocks(FF.dd_5,{{2,2}},{{2,3}})

///

isComplexMap = D -> (
    A := source D;
    B := target D;
    deg = degree D;
    isWellDefined D;
    (lo,hi) := concentration A;
    for i from lo+1 to hi do --make sure D is a map of complexes!
        assert(B.dd_(i+deg)*D_i  ==  D_(i-1)*A.dd_i)
    )

beginDocumentation()

doc ///
Key
  AInfinity
Headline
  Compute the A-infinity structures on free resolutions
Description
  Text
   Following Burke's paper "Higher Homotopies and Golod Rings":
   Given an S-free resolution A -> R = S/I, set B = A_+[1] (so that B_m = A_(m-1) for m >= 2, B_i = 0 for i<2),
   and alternate differentials have changed sign.
   
   The A-infinity structure  is a sequence of degree -1 maps m_n: B^(**n) \to B such that
   m_1 is the differential, 
   mR2 is the multiplication (which is a homotopy B**B \to B lifting the degree -2 map
   d**1 - 1**d: B_2**B_2 \to B_1 (which induces 0)
       
   m_n for n>2 is a homotopy for the negative of the sum of degree -2 maps of the form
   m_(n-i+1)(1**...** 1 ** m_i ** 1 **..**),
   with inserting m_i into each possible (consecutive) sub product, and i = 2...n-1.
   Here m_1 represents the differential both of B and of B^(**n).
  Example
   I = Grassmannian(1,5, CoefficientRing => ZZ/32003); numgens(I)
   S = ring(I)
   M = S^1/I
   R = S/I
   
   A = freeResolution M; betti A
   B = (complex apply(length A - 1, i -> -A.dd_(i+2)))[-2];
SeeAlso
///


TEST ///
-- test code and assertions here
-- may have as many TEST sections as needed
///

TEST///
S = ZZ/101[a,b,c]
K = complex koszul vars S
KK = labeledTensorComplex{K,K}
componentsAndIndices KK_5
assert(indices KK_5 == {{3, 2}, {2, 3}})
R = S/ideal a
KKl = labeledTensorComplex(R,KK)
assert(indices KKl_1 =={0, 1})
///

///
restart
debug loadPackage "AInfinity"
S = ZZ/101[a,b,c]
R = S/ideal"a3,b3,c3"
M = coker vars R
n = 3
BB = burkeData(M,n)
assert(BB_2 == S^{3:-2}++S^{3:-3})
assert (indices BB_2 == {{2}, {2, 0}})
assert (source (BB_2_[{2,0}]) == S^{3:-3})
///

TEST///
debug needsPackage "AInfinity"
S = ZZ/101[a,b]
X = labeler(A,S^1)
Y = labeler(B,S^2)
C = labeledDirectSum {X,Y}
--D = labeledDirectSum(S, {},{})
--D^[{}]
assert (componentsAndIndices C  == ({S^1, S^2}, {A,B}))
assert(componentsAndIndices C == ({S^1 , S^2 }, {A, B}))
assert(C^[A] == map(S^1,S^3,{{1,0,0}}))
assert(label components C == {A,B})
assert(indices C == {A,B})
///

TEST///
S = ZZ/101[a,b,c]
K' = complex koszul vars S

K = labeledTensorComplex K' --this should work!
assert(label K_2 == {2})
assert(K_0_[{0}] == map(S^1,S^1,id_(S^1)))

K2 = labeledTensorComplex({K',K'}, LengthLimit => 3)
picture K2
componentsAndIndices(K2_1)
assert(K2_1_[{1,0}] == map(S^{6:-1},S^{3:-1},id_(S^{3:-1})||0*id_(S^{3:-1})))
assert(max K2 == 3)

R = S/ideal a
RK = labeledTensorComplex(R,K)
picture RK
assert(label RK_2 == {2})
assert(RK_0_[{0}] == map(R^1,R^1,1))
///

TEST///

kk = ZZ/101
S = kk[x,y,z]
I = ideal"x2,y2,z2"*(ideal vars S)
R =S/I
mA = aInfinity R
mG = aInfinity(mA,coker vars R)
F = burke(R,coker vars R,3)
assert (F.dd^2==0)
assert all(5, i-> prune HH_(i+1)F == 0)

picture (F.dd_2*F.dd_3)
mapComponents {2,1}
A1 = extractBlocks(F.dd_3, {{2,0}},{{2,1}})
A2 = extractBlocks(F.dd_3, {{2}},{{2,1}})

B1 = extractBlocks(F.dd_2, {{1}}, {{2,0}})
B2 = extractBlocks(F.dd_2, {{1}},{{2}})

C1 = B1*A1
C2 = B2*A2
C1-C2
///

end--
///
--necessity of double labeling:
C = labeler(A,S^1) ++ labeler(B,S^2)
componentsAndIndices C
picture id_C
--but
C_[A]
--does not work!

C = (A =>labeler(A,S^1)) ++ (B =>labeler(B,S^2))
componentsAndIndices C
picture id_C
--work, AND
C_[A] -- works

C = (A =>S^1) ++ (B => S^2)
componentsAndIndices C -- does not work
picture id_C -- does not work
--but
C_[A] -- works
///




-*
TODO: 

Make aInfinity Ring use the commutative multiplication. 
Is there an analogue for the higher products?
can we call SchurComplexes?

add associativities


Note: from "Grammarly":
"Labeled and labelled are both correct spellings, 
and they mean the same thing. 
How you spell the word depends on your audience. 
If you are writing for American readers, labeled is the preferred spelling. 
In other places, such as Great Britain and Canada, 
labelled is a more common spelling than labeled."

also: labeled gets 5X more hits in google than labelled.

*-
S = ZZ/101[a,b,c]
B = apply(4, i-> S^{1+i:i})
A = B_0**B_1**(B_2++B_3)
formation (A.cache.formation#1#1)
oo.cache.indices
A.cache.indices 

labeledTensorChainComplex = method()
labeledTensorChainComplex List := ChainComplex => L -> (
    --L = {C_0..C_(p-1)}, list chain complexes. Form the tensor product of the C_i
    --in such a way that if the tensor products of the modules (C_i)_m are labeled,
    --then the modules of the tensor product are direct sums of modules from the hashtable, so that
    --componentsAndIndices applied to pC gives the correct list of indices, and
    --thus picture pC.dd_m works.
    if class L_0 =!= ChainComplex then error"Input should be a list of ChainComplexes.";
    S := ring L_0;
    if #L == 1 and class L_0 === ChainComplex then (
	B := L_0;
	F := for i from min B to max B list labeler({i}, B_i);
	B' := complex for i from min B to max B -1 list map(F_(i-min B),F_(i+1-min B), B.dd_(i+1));
	return B'[-min B]
        );
    p := #L;
    Min := apply(L, C->min C);
    Max := apply(L, C->max C-1);
    modules := apply(#L + sum Max - sum Min, i ->(
	    d := i+sum Min;
	    com := select(compositions(p,d), c -> all(p, i->Min_i <= c_i and c_i<= Max_i) and c != {});
	    apply(com, co -> (co => labeler(co, tensor(S,apply(p, pp->(L_pp)_(co_pp))))))
	));
    modules = select(modules, tt-> #tt != 0);

suitable := v-> if min v == 0 then position (v, vv -> vv == 1) else null;
     -- v is a list of ZZ. returns null unless v has the form
     -- {0...0,1,0..0}, in which case it returns the position of the 1.

    d := for i from 0 to #modules -2 list(	
        map(directSum modules#i,
            directSum modules#(i+1),
            matrix table( -- form a block matrix
                modules#i, -- rows of the table
                modules#(i+1), -- cols of the table
                (j,k) -> ( -- j,k each have the form (List => Module)
		    indtar := j#0;
		    indsrc := k#0;		    
                    tar := j#1;
                    src := k#1;
		    p := suitable(indsrc - indtar);
                    m := map(tar, src, 
			if p === null then 0 else(
			sign := (-1)^(sum(indsrc_(toList(0..p-1))));
			phi := sign*(tensor(S, apply(p, q -> L_q_(indtar_q)))**
			                                (L_p).dd_(indsrc_p)**
                               tensor(S, apply(#L-p-1, q -> L_(p+q+1)_(indtar_(p+q+1)))))
			))))));
                   (chainComplex d)[-sum(L, ell -> min ell)])
B
G
labeledTensorChainComplex{chainComplex B,chainComplex G}
labeledTensorComplex{B,G}
B**G
lTC{B,G}
lTC{G,G}
G**G
lTC{B,B}
B**B
lTC{B,B,G}
B**B**G

----------
--Roos example: non-Golod with trivial homology algebra.
restart
needsPackage "DGAlgebras"
debug needsPackage "AInfinity"
kk = ZZ/101
--kk = QQ
S = kk[x,y,z,u]
I = ideal(u^3, x*y^2, (x+y)*z^2, x^2*u+z*u^2, y^2*u+x*z*u, y^2*z+y*z^2) -- has the betti nums as in Roos
betti (A = res I) -- shows that the m_2 must be trivial
R = S/I
isGolod R -- gives the wrong answer! as one sees by comparing Poincare series, below
H = acyclicClosure(R, EndDegree => 0)
isHomologyAlgebraTrivial H

betti res( coker vars R, LengthLimit =>5)
--golodRanks(coker vars R, 5)
((1+t)^4)*sum(10, i-> (6*t^2+12*t^3+9*t^4+2*t^5)^i)

m = aInfinity R;
trim ideal(m#{2,2,2})
-----Roos examples!
needsPackage"DGAlgebras"
kk = ZZ/101
S = kk[u,x,y,z]
use S
II = {I1 = ideal(u^3, x*y^2, (x+y)*z^2, x^2*u+z*u^2, y^2*u+x*z*u, y^2*z+y*z^2),
-- kSS(R,7)={3,4,5}
I2= ideal"u3,y2u2,z2u2,y2zu,xy2,(x+y)z2,x2yz,x2u",
-- kSS(R,7)={0}
I3=ideal"u3,y2u2,z2u2,y2zu,xy2,(x+y)z2,x2yz,x2u+xyu",
-- kSS(R,7)={0}
I4=ideal"u3, y2u2, z2u2, y2zu, xy2, (x + y)z2, x2yz, x2u + zu2",
-- kSS(R,7)={0}
-- the next two has only cubics
I5=ideal"u3, xy2,(x+y)z2, x2u + zu2, y2u + xzu, y2z + yz2",
-- kSS(R,7)={3,4,5}
I6= ideal"u3, x2u, xz2 + yz2, xy2, x2y+y2u, y2z+z2u"}
-- kSS(R,7)={4,5,6}

netList for I in II list(
H = acyclicClosure(S/I, EndDegree => 0);
isGolod(S/I), isHomologyAlgebraTrivial(H))

--needs 1459.9 sec
--elapsedTime kSS(S/I6, 8) == {4, 5, 6, 7}

