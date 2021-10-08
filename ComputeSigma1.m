// ComputeSigma1.m
// Given data from "count_sextic_forms", computes sigma1 and sigma1^*

// assume data file already loaded
// load "CountSextics7.data";

// Compute lifting probabilities

// nu - for lifting double roots
nu := (3*p^4 - p^3 + p^2 - 3*p + 6)/(6*p^5);

// pi - for lifting triple roots
if p eq 7 then
    pi := 17694619/141229221;
else
    pi := (3*p^6 + 3*p^4 + 3*p^3 + p^2 + 1)/(3*(p^4 + p^3 + p^2 + p + 1)*p^3);
end if;

// initialize with c0 data 
// (check to make sure c0 is first entry, but it typically finishes quickest)
total := data[1][2];
count_hensel := data[1][3];
count_insoluble := data[1][4];

total_star := data[1][11];
count_star_hensel := data[1][12];
count_star_insoluble := data[1][13];

total_case1 := data[1][20];
count_case1_hensel := data[1][21];
count_case1_insoluble := data[1][22];
count_case1_double := data[1][23];
count_case1_double2 := data[1][24];
count_case1_double3 := data[1][25];
count_case1_triple := data[1][26];

total_star1 := data[1][29];
count_star1_hensel := data[1][30];
count_star1_insoluble := data[1][31];
count_star1_double := data[1][32];
count_star1_double2 := data[1][33];
count_star1_double3 := data[1][34];
count_star1_triple := data[1][35];

// add in rest of data - use multiplier (p-1)/6
for i in [2 .. 7] do
	total := total + ((p-1)/6)*data[i][2];
	count_hensel := count_hensel + ((p-1)/6)*data[i][3];
	count_insoluble := count_insoluble + ((p-1)/6)*data[i][4];

	total_star := total_star + ((p-1)/6)*data[i][11];
	count_star_hensel := count_star_hensel + ((p-1)/6)*data[i][12];
	count_star_insoluble := count_star_insoluble + ((p-1)/6)*data[i][13];

	total_case1 := total_case1 + ((p-1)/6)*data[i][20];
	count_case1_hensel := count_case1_hensel + ((p-1)/6)*data[i][21];
	count_case1_insoluble := count_case1_insoluble + ((p-1)/6)*data[i][22];
	count_case1_double := count_case1_double + ((p-1)/6)*data[i][23];
	count_case1_double2 := count_case1_double2 + ((p-1)/6)*data[i][24];
	count_case1_double3 := count_case1_double3 + ((p-1)/6)*data[i][25];
	count_case1_triple := count_case1_triple + ((p-1)/6)*data[i][26];

	total_star1 := total_star1 + ((p-1)/6)*data[i][29];
	count_star1_hensel := count_star1_hensel + ((p-1)/6)*data[i][30];
	count_star1_insoluble := count_star1_insoluble + ((p-1)/6)*data[i][31];
	count_star1_double := count_star1_double + ((p-1)/6)*data[i][32];
	count_star1_double2 := count_star1_double2 + ((p-1)/6)*data[i][33];
	count_star1_double3 := count_star1_double3 + ((p-1)/6)*data[i][34];
	count_star1_triple := count_star1_triple + ((p-1)/6)*data[i][35];
end for;

// compute sigma1
sigma1 := (count_case1_hensel + count_case1_double*nu + count_case1_double2*(1-(1-nu)^2) + count_case1_double3*(1-(1-nu)^3) + count_case1_triple*pi)/total_case1;
sigma1star := (count_star1_hensel + count_star1_double*nu + count_star1_double2*(1-(1-nu)^2) + count_star1_double3*(1-(1-nu)^3) + count_star1_triple*pi)/total_star1;

print "p =", p;
print "";
print "totals";
print "total:       ", total;
print "hensel:      ", count_hensel;
print "insol:       ", count_insoluble;
print "rho_bound:   ", count_hensel/total;
print "approx:      ", RealField()!(count_hensel/total);
print "";

print "star";
print "total:       ", total_star;
print "hensel:      ", count_star_hensel;
print "insol:       ", count_star_insoluble;
print "rho*_bound:  ", count_star_hensel/total_star;
print "approx:      ", RealField()!(count_star_hensel/total_star);
print "";

print "case1";
print "total:       ", total_case1;
print "hensel:      ", count_case1_hensel;
print "insol:       ", count_case1_insoluble;
print "(1^2):       ", count_case1_double;
print "(1^21^2):    ", count_case1_double2;
print "(1^21^21^2): ", count_case1_double3;
print "(1^3):       ", count_case1_triple;
print "sigma1:      ", sigma1;
print "approx:      ", RealField()!sigma1;
print "";

print "star1";
print "total:       ", total_star1;
print "hensel:      ", count_star1_hensel;
print "insol:       ", count_star1_insoluble;
print "(1^2):       ", count_star1_double;
print "(1^21^2):    ", count_star1_double2;
print "(1^21^21^2): ", count_star1_double3;
print "(1^3) :      ", count_star1_triple;
print "sigma1star:  ", sigma1star;
print "approx:      ", RealField()!sigma1star;
