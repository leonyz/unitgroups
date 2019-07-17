newPackage("UnitGroups",
	AuxiliaryFiles => true,
	Version => "0.0.1",
	Date => "October 22, 2018",
	Authors => {{
		Name => "Justin Chen",
		Email => "jchen646@gatech.edu",
		HomePage => "https://people.math.gatech.edu/~jchen646"}},
	Headline => "a package for computing unit groups",
	HomePage => "https://math.berkeley.edu/~leonyz/code/",
	PackageExports => {},
	DebuggingMode => false
)
export {
	"certifyLift",
	"boundaryPts",
	"liftRationalFunction",
	"reduceSquares",
	"planeConicUnits",
	"parametricLift",
	"rationalCurveUnits",
	"clearDenom",
	"reduceGCD"
}

certifyLift = method() -- Algorithm 3.6 (Clearing denominators)
certifyLift (RingElement, RingElement, Ideal) := RingElement => (f, g, I) -> (
	local J, local C;
	if not(ring f === ring g and ring f === ring I) then error "Expected same rings";
	J = (matrix{{g}} | gens I);
	C = matrix{{f}} // J;
	if (J*C)_(0,0) == f then C else ( print "Cannot lift rational function"; false )
)

isUnit (Ideal, RingElement) := (I, h) -> 1 % (I + ideal sub(h, ring I)) == 0 -- Algorithm 3.8 (Testing units)

liftRationalFunction = method() -- Algorithm 3.10 (Computing preimages)
liftRationalFunction (RingElement, RingElement, Ideal) := RingElement => (F, G, I) -> (
	local t, local T, local IT, local f, local g, local h;
	T = (coefficientRing ring F)(monoid[gens ring F, getSymbol "u"]); -- newRing ring F;
	IT = ideal(product gens T - 1) + sub(I, T);
	(f, g) = (F, G)/(p -> sub(p, T));
	h = certifyLift(f, g, IT);
	if not h === false and isUnit(IT, h_(0,0)) then return (h_(0,0) % IT);
	false
)

boundaryPts = method()
boundaryPts RingElement := List => F -> ( -- plane conic case
	if not #gens ring F == 3 then error "Expected plane curve";
	local R, local kk, local randCoord, local specializations, local X, local Y, local K;
	local sq, local discList, local rootList, local a, local b, local c, local D, local s;
	R = ring F;
	kk = coefficientRing R;
	randCoord = random ZZ;
	specializations = apply(gens R, Z -> (
		(X, Y) = toSequence delete(Z, gens R);
		sub(sub(F, {Y => 1, Z => 0}), kk(monoid[X]))
	)); -- | {sub(sub(F, {Y => 1 + randCoord, last gens R => 1}), kk(monoid[X]))};
	K = kk;
	sq = symbol sq;
	discList = {};
	rootList = for G in specializations list (
		X = first support G;
		(a,b,c) = toSequence flatten entries last coefficients(G, Monomials => {X^2, X, 1}) /(e -> lift(e, kk));
		if not(a == 0) then (
			D = reduceSquares factor lift(b^2 - 4*a*c, kk);
			s = D#0*(if (D#1 == 0 or D#1 == 1) then (D#1)_K
			else if member(D#1, discList) then sub(sq_(D#1), K)
			else (
				discList = append(discList, D#1);
				K = kk[discList/(d -> sq_d)]/ideal(discList/(d -> sq_d^2 - d));
				last gens K
			));
			(1/(2*a))*(unique {-b + s, -b - s})
		) else {(1/b)*(-c)}
	);
	unique((apply(rootList#0, r -> {0, sub(r, K), 1}) | 
	apply(rootList#1, r -> {sub(r, K), 0, 1}) | 
	apply(rootList#2, r -> {sub(r, K), 1, 0})) /(p -> matrix{p}))
)
boundaryPts Matrix := List => M -> ( -- parametrized rational curve case
	local bdyPolys, local linForms, local exts, local r, local S, local K, local j;
	bdyPolys = flatten apply(flatten entries M, e -> (toList apply(factor e, toList))/first);
	linForms = select(bdyPolys, p -> first degree p == 1);
	exts = select(bdyPolys, p -> first degree p > 1);
	r = getSymbol "root";
	S = if #exts > 0 then (
		K = (coefficientRing ring M)(monoid [apply(#exts, i -> r_i)]);
		(K/ideal apply(#exts, i -> (map(K, ring exts#i, {K_i, 1}))(exts#i)))[gens ring M]
	) else ring M;
	unique(apply(linForms, l -> sub(transpose gens ker transpose last coefficients(l, Monomials => gens ring l), S)) | apply(#exts, j -> matrix{{K_j, 1_S}}))
)

planeConicUnits = method() -- Algorithm 4.6 (Computing unit groups of conics)
-- Returns units in a new ring with u = (xyz)^{-1}
planeConicUnits (RingElement, List, Matrix) := List => (f, pts, B) -> (
	if not first degree f == 2 then error "Expected conic (degree 2)";
	local S, local supp, local p, local coordIndex, local coordPts, local P, local L;
	S = ring f;
	apply(numcols B, j -> (
		supp = positions(flatten entries B_j, i -> i != 0);
		if B_(supp#0,j) < 0 then supp = reverse supp;
		p = pts#(supp#1);
		coordIndex  = position(toList(0..<numcols p), i -> p_(0,i) == 0);
		coordPts = select(pts, q -> q_(0, coordIndex) == 0);
		P = first (if #coordPts > 1 then delete(p, coordPts) else coordPts);
		if P == pts#(supp#0) then P = pts#((toList(0..<numrows B) - set supp)#0);
		liftRationalFunction(det(vars S || pts#(supp#0) || P), S_coordIndex, ideal f)
		-- liftRationalFunction(det(vars S || pts#(supp#0) || P), det(vars S || p || P), sub(ideal f, S))
	))
)
planeConicUnits RingElement := List => f -> (
	pts := boundaryPts f;
	B := matrix table(#pts, #pts-1, (i,j) -> if i == j then 1 else if i == j+1 then -1 else 0);
	S := (ring pts#0)(monoid[gens ring f]);
	planeConicUnits(sub(f, S), pts/(p -> sub(p, S)), B)
)

parametricLift = method() -- Algorithm 5.2 (Subalgebra membership)
parametricLift (RingElement, RingElement, Matrix) := RingElement => (f, g, M) -> (
	local n, local S, local invg, local y, local z, local N, local J, local h;
	(invg,y,z) = ("invg","y","z")/getSymbol;
	n = numcols M - 1;
	S = (coefficientRing ring f)[gens ring f, invg, y_0..y_n, z_0..z_n, MonomialOrder => Lex];
	N = flatten entries sub(M, S);
	J = ideal(flatten apply(#N, i -> {S_(i+3) - N_i, S_(i+4+n)*N_i - 1})) + ideal(sub(g, S)*(S_2) - 1);
	h = (sub(f, S)*(S_2)) % (gens gb J);
	if not member(S_2, support h) then h else false
)

rationalCurveUnits = method()
rationalCurveUnits (Matrix, List, Matrix) := List => (M, pts, B) -> (
	local S, local posSupp, local negSupp, local F, local G;
	S = ring M;
	if #gens S != 2 then error "Expected parametrized rational curve";
	apply(numcols B, j -> (
		posSupp = positions(flatten entries B_j, i -> i > 0);
		negSupp = positions(flatten entries B_j, i -> i < 0);
		F = product apply(posSupp, i -> ((pts#i)_(0,1)*(S_0) - (pts#i)_(0,0)*(S_1))^(B_(i,j)));
		G = product apply(negSupp, i -> ((pts#i)_(0,1)*(S_0) - (pts#i)_(0,0)*(S_1))^(-B_(i,j)));
		parametricLift(F, G, M)
	))
)
rationalCurveUnits Matrix := List => M -> (
	pts := boundaryPts M;
	B := matrix table(#pts, #pts-1, (i,j) -> if i == j then 1 else if i == j+1 then -1 else 0);
	rationalCurveUnits(sub(M, ring pts#0), pts, B)
)

radical ZZ := opts -> a -> value apply(factor a, p -> first p)

reduceSquares = method() -- returns pair (a, b) such that q = (a^2)*b with b squarefree
reduceSquares Product := Sequence => q -> ( -- q should be of the form factor(n)
	a := apply(q, pow -> Power{pow#0, pow#1 // 2});
	b := apply(q, pow -> Power{pow#0, pow#1 % 2});
	(a, b)/value
)
reduceSquares Divide := Sequence => q -> (
	(n, d) := (numerator q, denominator q)/reduceSquares;
	((n#0)/(d#0), (n#1)/(d#1))
)

clearDenom = method()
clearDenom RingElement := RingElement => f -> f * lcm(flatten entries(sub(last coefficients f, coefficientRing ring f)) /denominator)

reduceGCD = method()
reduceGCD RingElement := RingElement => f -> f // gcd(flatten entries(sub(last coefficients f, coefficientRing ring f)) /numerator)


TEST ///
R = QQ[t,x,y]
I = ideal(x^2 + y^2 - 1, 1 - t*x*y)
C = certifyLift(1_R, 1+x, I)
assert((matrix{{1+x}} | gens I) * C == matrix{{1_R}})
assert(certifyLift(1_R, 2+x, I) === false)
///

TEST ///
R = QQ[x,y,z]
f = random(2, R)
f = (basis(2, R)*random(ZZ^6, ZZ^1))_(0,0)
f = 4*x^2+2*x*y+3*y^2+5*x*z+5*y*z+z^2
f = 3*x^2+4*x*y+y^2+9*x*z+3*y*z+5*z^2 -- random point {y => 5/4, z => 1}
f = 8*x^2+2*x*y+2*x*z+5*y*z+6*z^2
#planeConicUnits f == 4
f = x^2 + y^2 - z^2 -- Fermat curve: Example 4.8
f = x^2 + y*z -- fails: needs non-boundary point
boundaryPts f
U = planeConicUnits f
S = ring U#0
assert(all(U, u -> 1 % (ideal sub(u, S) + ideal(sub(f, S)) + ideal(product gens S - 1)) == 0))
-- Singular conics: can (and should) give errors
(try boundaryPts x^2) === null
(try boundaryPts x*y) === null
g = x^2 + 2*x*y + y^2 - z^2 -- union of two lines
planeConicUnits g
///

TEST ///
k = frac(QQ[t])
R = k[x,y,z]
f = (1+t)*(x^2 + y^2 + z^2) - ((1+t)^2 + 1)*(x*y + y*z + z*x) -- Example 4.9
time U = planeConicUnits f -- (note: different basis of Div^0_\partial)
U/clearDenom/reduceGCD
assert(#U == 5)
pts = flatten(pack(2, boundaryPts f)/reverse)
B = transpose matrix{{-1,0,1,0,0,0},{0,-1,1,0,0,0},{0,0,-1,0,1,0},{0,0,0,-1,1,0},{-1,0,0,0,0,1}}
U = planeConicUnits(f, pts, B) /clearDenom/reduceGCD
T = ring U#0
J = sub(ideal f, T) + ideal(product gens T - 1)
(h0, h1) = (sub(clearDenom det(vars R || pts#4 || pts#3), T), T_1)
assert((sub(U#2, T)*h1 - h0) % J == 0) -- divisor P_5 - P_3
(h0, h1) = (sub(clearDenom det(vars R || pts#4 || pts#2), T), T_1)
assert((sub(U#3, T)*h1 - h0) % J == 0) -- divisor P_5 - P_4
///

TEST ///
R = QQ[s,t]
M = matrix{{s^3 - 4*s*t^2, s^2*t - 9*t^3, (s-3*t)*t^2, (s+3*t)*t^2}}
M = matrix{{random(1,R)*random(2,R), random(1,R)*random(1,R)*random(1,R), random(3,R)}}
M = random(R^1, R^{9:-4})
boundaryPts M
rationalCurveUnits M
pts = (boundaryPts M)_{0,3,4,5,1,2}
S = ring pts#0
assert(all(pts, p -> member(0_S, flatten entries sub(M, p))))
B = matrix{{1,0,0,0,0},{-2,1,0,0,0},{0,-1,1,0,0},{-1,0,-1,1,0},{1,0,0,-1,1},{1,0,0,0,-1}}
rationalCurveUnits(M, pts, B)
///

end--

restart
loadPackage("UnitGroups", Reload => true)
uninstallPackage "UnitGroups"
installPackage "UnitGroups"
installPackage("UnitGroups", RemakeAllDocumentation => true)
viewHelp "UnitGroups"
check "UnitGroups"
