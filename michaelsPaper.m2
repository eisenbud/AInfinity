needsPackage "MCMApproximations"


testNS = (n,s) ->(
R = ZZ/101[x_0..x_(n-2),y_0..y_s];
N = matrix{{x_0..x_(n-2),0},{0,x_0..x_(n-2)}};--nilp block, size n
S = matrix{{y_0..y_(s-1)},{y_1..y_s}};--scroll block, size s
M = N|S;
I = minors(2,M)
)


--- Finds examples where the statement 
--- reg I = max of 2 and floor(n/s)+1
--- is false.
--- {{5, 3}, {6, 4}, {7, 4}, {7, 5}}
toList delete(,apply({2,2}..{7,7},L->(
	I = testNS(L#0,L#1);
	if regularity I != max{2,floor((L#0)/(L#1))+1} then L
	)))


--- Finds examples where the statement 
--- reg I = max of 2 and highest degree socle +1
--- is false.
--- No such examples.
toList delete(,apply({2,2}..{7,7},L->(
	I = testNS(L#0,L#1);
	M = R^1/I;
	m = max socleDegrees M;
	if regularity I != max{2,m+1} then L
	)))


--- Finds examples where the statement 
--- highest degree socle = floor(n/s)+1
--- is false.
--- Many...  {5, 2}, {5, 4}, {5, 5}...
toList delete(,apply({2,2}..{7,7},L->(
	I = testNS(L#0,L#1);
	M = R^1/I;
	m = max socleDegrees M;
	if m != floor((L#0)/(L#1))+1 then L
	)))


--- Finds examples where the statement 
--- highest degree socle = largest d such 
--- that (hilbertFunction(d,S/I) - hilbertFunction(d,S'/I')) \neq 0
--- is false.
--- No such examples.
toList delete(,apply({2,2}..{7,7},L->(
	I = testNS(L#0,L#1);
	M = R^1/I;
	m = max socleDegrees M;
	L1 = apply(10,i->hilbertFunction(i,M));
	I = testNS(0,L#1);
	M = R^1/I;
	L2 = apply(10,i->hilbertFunction(i,M));
	L3 = L1-L2;
	maxDis = max delete(,apply(L3,i->if i!=0 then position(L3,k->k==i)));
	if m != maxDis then L
	)))


--- (n,s) = (5,3)
I = testNS(5,3);
--- reg = 3 != 2 
regularity I
max{2,floor(5/3)+1}
---
M = R^1/I;
--- max socle degree == 2
max socleDegrees M
apply(10,i->hilbertFunction(i,HH^0(M)))
L1 = apply(10,i->hilbertFunction(i,M));
---
I = testNS(0,3);
M = R^1/I;
L2 = apply(10,i->hilbertFunction(i,M));
--- last difference is 2 == max Socle degree == floor(n/s)+1
L3 = L1-L2


--- (n,s) = (5,4)
I = testNS(5,4);
--- reg = 2 == 2 
regularity I
max{2,floor(5/4)+1}
---
M = R^1/I;
--- max socle degree == 1
max socleDegrees M
apply(10,i->hilbertFunction(i,HH^0(M)))
L1 = apply(10,i->hilbertFunction(i,M));
---
I = testNS(0,4);
M = R^1/I;
L2 = apply(10,i->hilbertFunction(i,M));
--- last difference is 1 == max socle degree != floor(n/s)+1
L3 = L1-L2


