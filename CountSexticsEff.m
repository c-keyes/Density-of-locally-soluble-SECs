/*
CountSexticsEff.m

Christopher Keyes
Updated September 6, 2021

Magma routines for efficiently enumerating sextic forms f(x,z) over Fp taking a value liftable
by Hensel's lemma to a Qp-point of y^3 = f(x,z).

Note these routines are easily modifiable to exponents m other than 3 and degrees d other than 6
*/

/*
setup(p): produces a list of cubic residues modulo p and a cubic nonresidue

INPUTS: p
	- p is a prime. 

OUTPUTS: cubes, noncube
	- cubes is a list of cubic residues modulo p
	- noncube is a cubic nonresidue. If p = 1 (3), it is nonzero. If p = 2 (3), it will be 0.
*/
setup := function(p)
	// generate list of cubic residues
    cubes := {1};								// 1 is always a cube
    for i in [1 .. p-1] do
        Include(~cubes, (i^3 mod p));			// add to list
    end for;

    // return first nonzero cubic residue if p = 1 (3), or zero if p = 2 (3)
	noncube := 0;
    for i in [1 .. p-1] do
        if not(i in cubes) then
            noncube := i;
            break;
        end if;
    end for;

    return cubes, noncube;
end function;

/*
has_cube_val(p,f,cubes): detects whether f(x,z) takes a value in the nonzero cubic residues
						 modulo p, (Fp^*)^3

INPUTS: p
	- p is a prime
	- f is a binary sextic form f(x,z) over Fp.
	- cubes is the list of nonzero cubic residues modulo p (see setup(p) above)

OUTPUTS: boolean
	- returns true if f(x,z) takes some value in cubes
	- returns false if not
*/
has_cube_val := function(p,f,cubes)
	// first check the point at infinity
    if Evaluate(f, [1,0]) in cubes then
        return true;
    end if;

    // check all affine values [x:1]
    for i in [0 .. p-1] do
        if Evaluate(f, [i,1]) in cubes then
            return true;
        end if;
    end for;

    return false;
end function;

/*
has_simple_root(p,f): detects whether f(x,z) has a simple root, i.e. a root over Fp of
						multiplicity one

INPUTS: p
	- p is a prime
	- f is a binary sextic form f(x,z) over Fp.

OUTPUTS: boolean
	- returns true if f(x,z) has a root of multiplicity one
	- returns false if f(x,z) does not have such a root
*/
has_simple_root := function(p,f)
	// first check the point at infinity
    if (Evaluate(f, [1,0]) eq 0) and not (Evaluate(Derivative(f,2), [1,0]) eq 0) then
        return true;
    end if;

    // check all affine values [x:1]
    for i in [0 .. p-1] do
        if (Evaluate(f, [i,1]) eq 0) and not (Evaluate(Derivative(f,1), [i,1]) eq 0) then
            return true;
        end if;
    end for;

    return false;
end function;

/*
is_cube_poly(p,f): detects whether f(x,z) is a cube in Fp[x,z], i.e. f(x,z) = h(x,z)^3
				   for some binary quadratic form h(x,z)

INPUTS: p
	- p is a prime
	- f is a binary sextic form f(x,z) over Fp.

OUTPUTS: boolean
	- returns true if f(x,z) = h(x,z)^3 for some h
	- returns false if not
*/
is_cube_poly := function(p,f)
	// factor f, and for each factor, check if the exponent is divisible by 3
    for i in [1 .. #Factorization(f)] do
    	// if any exponent is not divisible by 3, return false
        if not Factorization(f)[i][2] mod 3 eq 0 then
            return false;
        end if;
    end for;

    // reaching here means each factor is divisible by 3, hence f(x,z) is a cube
    return true;
end function;

/*
set_case1_flag(p,f): wrapper for is_cube_poly(p,f), converting true/false into 0/1

INPUTS: p
	- p is a prime
	- f is a binary sextic form f(x,z) over Fp.

OUTPUT: returns 1 if is_cube_poly(p,f) = false,
        returns 0 if is_cube_poly(p,f) = true or f = 0 (mod p)
*/
set_case1_flag := function(p,f)
    if f eq 0 then
        return 0;
    end if;

    if is_cube_poly(p,f) then
        return 0;
    end if;
    return 1;
end function;

/*
set_cube_flag(p,f): wrapper for has_cube_val(p,f), converting true/false into 1/0

INPUTS: p
	- p is a prime
	- f is a binary sextic form f(x,z) over Fp.

OUTPUT: returns 1 if f(x,z) takes a nonzero cubic residue value,
        returns 0 if f(x,z) doesn't take a nonzero cubic residue value
*/
set_cube_flag := function(p,f,cubes)
    if has_cube_val(p,f,cubes) then
        return 1;
    end if;

    return 0;
end function;

/*
set_cube_flag(p,f): wrapper for has_simple_root(p,f), converting true/false into 1/0

INPUTS: p
	- p is a prime
	- f is a binary sextic form f(x,z) over Fp.

OUTPUT: returns 1 if f(x,z) has a root in Fp of multiplicity 1,
        returns 0 if f(x,z) doesn't have such a root
*/
set_root_flag := function(p,f)
    if has_simple_root(p,f) then
        return 1;
    end if;

    return 0;
end function;

/*
count_sextic_forms(p,c0): procedure to count the number of sextic forms f(x,z) over Fp
 			possessing an Fp point which lifts to a Qp point via Hensel's Lemma. These
 			points arise either via a root of multiplicity 1 or a value [x:z] such that 
 			f(x,z) is a nonzero cubic residue modulo p. This is used to give a lower 
 			bound for rho_3,6(p).

 			Along the way, it is convenient to count the number of such forms also satisfying
			condition (*), in factorization case 1, and both, thus leading to lower bounds for
			rho^*(p), sigma_1(p), and sigma_1^*(p).

INPUTS: p
	- p is a prime
	- c0 is a residue in Fp which is is the constant term of the sextic forms f(x,z)

PRINTED VALUES: 
	- total: 		the total number of binary sextic forms f(x,z) with constant term c0
	- count_cube:	the number of forms taking a nonzero cubic residue value
	- count_root:   the number of forms possessing a root of multiplicity one
	- count_both:   the number of forms with both a cubic value and a root
	- total_star:   the number of forms satisfying (*) (analogously have count_star_cube,
						count_star_root, and count_star_both)
	- total_case1:  the number of forms satisfying factorization case 1, i.e. f(x,z) is 
						not a cube in the ring Fp[x,z] (analogously have count_case1_cube,
						count_case1_root, and count_case1_both)
	- total_star1:  the number of forms satisfying (*) and case 1 (analogously have 
						count_star1_cube, count_star1_root, and count_star1_both)
*/
count_sextic_forms := procedure(p, c0)

    R<x,z> := PolynomialRing(GF(p), 2);
    cubes, noncube := setup(p);

    // Initialize all counters

    // totals
    total := 0;
    total_star := 0;
    total_case1 := 0;
    total_star1 := 0;

    // cubes
    count_cube := 0;
    count_star_cube := 0;
    count_case1_cube := 0;
    count_star1_cube := 0;

    // roots
    count_root := 0;
    count_star_root := 0;
    count_case1_root := 0;
    count_star1_root := 0;

    // cube + root
    count_both := 0;
    count_star_both := 0;
    count_case1_both := 0;
    count_star1_both := 0;

    // flags
    star_flag := 0;
    case1_flag := 0;
    root_flag := 0;
    cube_flag := 0;

    // loop through c1, ..., c5
    for c1 in [0 .. p-1] do
        for c2 in [0 .. p-1] do
            for c3 in [0 .. p-1] do
                for c4 in [0 .. p-1] do
                    for c5 in [0 .. p-1] do

                        // c6 = 0
                        f := c5*x^5*z + c4*x^4*z^2 + c3*x^3*z^3 + c2*x^2*z^4 + c1*x*z^5 + c0*z^6;
                        star_flag := 0;
                        case1_flag := set_case1_flag(p,f);
                        root_flag := set_root_flag(p,f);
                        cube_flag := set_cube_flag(p,f,cubes);

                        // counts for c6 = 0 (multiplicity 1)
                        total := total + 1;
                        total_star := total_star + star_flag;
                        total_case1 := total_case1 + case1_flag;
                        total_star1 := total_star1 + star_flag*case1_flag;

                        count_root := count_root + root_flag;
                        count_star_root := count_star_root + root_flag*star_flag;
                        count_case1_root := count_case1_root + root_flag*case1_flag;
                        count_star1_root := count_star1_root + root_flag*star_flag*case1_flag;

                        count_cube := count_cube + cube_flag;
                        count_star_cube := count_star_cube + star_flag*cube_flag;
                        count_case1_cube := count_case1_cube + cube_flag*case1_flag;
                        count_star1_cube := count_star1_cube + cube_flag*case1_flag*star_flag;

                        count_both := count_both + root_flag*cube_flag;
                        count_star_both := count_star_both + root_flag*cube_flag*star_flag;
                        count_case1_both := count_case1_both + root_flag*cube_flag*case1_flag;
                        count_star1_both := count_star1_both + root_flag*cube_flag*case1_flag*star_flag;
    
                        // c6 = cube
                        f := f + x^6;
                        star_flag := 0;
                        case1_flag := set_case1_flag(p,f);
                        root_flag := set_root_flag(p,f);
                        cube_flag := 1;

                        // counting for c6 = 1; multiply each count by (p-1)/3, accounting for the (p-1)/3 nonzero cubic resdiues
                        total := total + ((p-1)/3);
                        total_star := total_star + star_flag*((p-1)/3);
                        total_case1 := total_case1 + case1_flag*((p-1)/3);
                        total_star1 := total_star1 + star_flag*case1_flag*((p-1)/3);

                        count_root := count_root + root_flag*((p-1)/3);
                        count_star_root := count_star_root + root_flag*star_flag*((p-1)/3);
                        count_case1_root := count_case1_root + root_flag*case1_flag*((p-1)/3);
                        count_star1_root := count_star1_root + root_flag*star_flag*case1_flag*((p-1)/3);

                        count_cube := count_cube + cube_flag*((p-1)/3);
                        count_star_cube := count_star_cube + star_flag*cube_flag*((p-1)/3);
                        count_case1_cube := count_case1_cube + cube_flag*case1_flag*((p-1)/3);
                        count_star1_cube := count_star1_cube + cube_flag*case1_flag*star_flag*((p-1)/3);

                        count_both := count_both + root_flag*cube_flag*((p-1)/3);
                        count_star_both := count_star_both + root_flag*cube_flag*star_flag*((p-1)/3);
                        count_case1_both := count_case1_both + root_flag*cube_flag*case1_flag*((p-1)/3);
                        count_star1_both := count_star1_both + root_flag*cube_flag*case1_flag*star_flag*((p-1)/3);

						// c6 = noncube (leave root_flag, case1_flag alone)
                        f := noncube*f;
                        star_flag := 1;
                        cube_flag := set_cube_flag(p,f,cubes);

                        // counting for c6 = noncube; multiply each count by (p-1)/3, accounting for the (p-1)/3 elements in the coset noncube(Fp^*)^3
                        total := total + ((p-1)/3);
                        total_star := total_star + star_flag*((p-1)/3);
                        total_case1 := total_case1 + case1_flag*((p-1)/3);
                        total_star1 := total_star1 + star_flag*case1_flag*((p-1)/3);

                        count_root := count_root + root_flag*((p-1)/3);
                        count_star_root := count_star_root + root_flag*star_flag*((p-1)/3);
                        count_case1_root := count_case1_root + root_flag*case1_flag*((p-1)/3);
                        count_star1_root := count_star1_root + root_flag*star_flag*case1_flag*((p-1)/3);

                        count_cube := count_cube + cube_flag*((p-1)/3);
                        count_star_cube := count_star_cube + star_flag*cube_flag*((p-1)/3);
                        count_case1_cube := count_case1_cube + cube_flag*case1_flag*((p-1)/3);
                        count_star1_cube := count_star1_cube + cube_flag*case1_flag*star_flag*((p-1)/3);

                        count_both := count_both + root_flag*cube_flag*((p-1)/3);
                        count_star_both := count_star_both + root_flag*cube_flag*star_flag*((p-1)/3);
                        count_case1_both := count_case1_both + root_flag*cube_flag*case1_flag*((p-1)/3);
                        count_star1_both := count_star1_both + root_flag*cube_flag*case1_flag*star_flag*((p-1)/3);

                        // c6 = noncube^2 (leave root flag, case1 flag, star flag alone)
                        f := noncube*f;
                        cube_flag := set_cube_flag(p,f,cubes);

                        // counting for c6 = non^2; multiply each count by (p-1)/3, accounting for the (p-1)/3 elements in the coset noncube^2(Fp^*)^3
                        total := total + ((p-1)/3);
                        total_star := total_star + star_flag*((p-1)/3);
                        total_case1 := total_case1 + case1_flag*((p-1)/3);
                        total_star1 := total_star1 + star_flag*case1_flag*((p-1)/3);

                        count_root := count_root + root_flag*((p-1)/3);
                        count_star_root := count_star_root + root_flag*star_flag*((p-1)/3);
                        count_case1_root := count_case1_root + root_flag*case1_flag*((p-1)/3);
                        count_star1_root := count_star1_root + root_flag*star_flag*case1_flag*((p-1)/3);

                        count_cube := count_cube + cube_flag*((p-1)/3);
                        count_star_cube := count_star_cube + star_flag*cube_flag*((p-1)/3);
                        count_case1_cube := count_case1_cube + cube_flag*case1_flag*((p-1)/3);
                        count_star1_cube := count_star1_cube + cube_flag*case1_flag*star_flag*((p-1)/3);

                        count_both := count_both + root_flag*cube_flag*((p-1)/3);
                        count_star_both := count_star_both + root_flag*cube_flag*star_flag*((p-1)/3);
                        count_case1_both := count_case1_both + root_flag*cube_flag*case1_flag*((p-1)/3);
                        count_star1_both := count_star1_both + root_flag*cube_flag*case1_flag*star_flag*((p-1)/3);

                    end for;
                end for;
            end for;
        end for;
    end for;

    print "p =", p, "c0 =", c0;
    print "type, total, cube, root, both";
    print "total:", total, count_cube, count_root, count_both;
    print "star:", total_star, count_star_cube, count_star_root, count_star_both;
    print "case1:", total_case1, count_case1_cube, count_case1_root, count_case1_both;
    print "star1:", total_star1, count_star1_cube, count_star1_root, count_star1_both;
end procedure;