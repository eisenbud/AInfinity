


needsPackage "RandomIdeals"
linPart = method()

linPart RingElement := f -> sum select(terms f, i->(degree i)_0 == 1)

linPart Matrix := M -> map(target M, source M,(
        m := matrix(apply(numrows M, j -> apply(numcols M, i -> linPart M_(j,i))));
	if m == 0 then 0_(ring M) else m))

linPart ChainComplex := F -> chainComplex apply(length F -1, i -> (
    	tar = target F.dd_(i+1);
	sour = source F.dd_(i+1);
	map(tar, sour,if linPart F.dd_(i+1) == 0 then 0 else linPart F.dd_(i+1))
     ))
end--
restart
load "monomialLinearity.m2"
kk = ZZ/101
S = kk[x_1..x_5]--, SkewCommutative => true]

I = ideal apply (gens S, x ->x^2)
I = ideal(x_1^2, x_2*x_3)
I = randomMonomialIdeal((2,2,2,2,2),S)
R = S/I
J = ideal for i in {2,2,3} list random(i, R)

F = complete res(J, LengthLimit => 8)
length F
prune (HH_(length F - 2) linPart F)
betti F
