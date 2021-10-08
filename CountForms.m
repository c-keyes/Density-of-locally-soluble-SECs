/*
CountSexticsEff.m

Christopher Keyes
Updated October 8, 2021

Magma routines for enumerating binary forms f(x,z) over Fp taking a value liftable
by Hensel's lemma to a Qp-point of y^3 = f(x,z).

Includes three main routines, and several subfunctions:
    - count_sextic_forms:  efficiently counts sextic forms taking with points that lift
    - count_cubic_forms:   counts cubic forms with points that lift
    - count_quartic_forms: counts quartic forms with points that lift

Note these routines are easily modifiable to exponents m other than 3 and other degrees
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
has_affine_cube_val(p,f,cubes): detects whether f(x,z) takes an affine value in the nonzero 
                        cubic residues modulo p, (Fp^*)^3

INPUTS: p
    - p is a prime
    - f is a binary sextic form f(x,z) over Fp.
    - cubes is the list of nonzero cubic residues modulo p (see setup(p) above)

OUTPUTS: boolean
    - returns true if f(x,z) takes some value in cubes
    - returns false if not
*/
has_affine_cube_val := function(p,f,cubes)
    // skip checking infinity
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
count_double_roots(p,f): counts number of double roots a binary form has

INPUTS:
        - p is a prime
        - f is a binary form f(x,z) over Fp

OUTPUTS:
        - num_double is the number of double roots f has over Fp.
*/
count_double_roots := function(p,f)

    num_double := 0;
    Fact := Factorization(f);

    for i in [1 .. #Fact] do
        if (Fact[i][2] eq 2) and (Degree(Fact[i][1]) eq 1) then
            num_double := num_double + 1;
        end if;
    end for;

    return num_double;
end function;

/*
count_triple_roots(p,f): counts number of double roots a binary form has

INPUTS:
        - p is a prime
        - f is a binary form f(x,z) over Fp

OUTPUTS:
        - num_triple is the number of double roots f has over Fp.
*/
count_triple_roots := function(p,f)

    num_triple := 0;
    Fact := Factorization(f);

    for i in [1 .. #Fact] do
        if (Fact[i][2] eq 3) and (Degree(Fact[i][1]) eq 1) then
            num_triple := num_triple + 1;
        end if;
    end for;

    return num_triple;
end function;

/*
count_sext_roots(p,f): counts number of sextuple roots a binary form has

INPUTS:
        - p is a prime
        - f is a binary form f(x,z) over Fp

OUTPUTS:
        - num_sext is the number of sextic roots f has over Fp.
*/
count_sext_roots := function(p,f)

    num_sext := 0;
    Fact := Factorization(f);

    for i in [1 .. #Fact] do
        if (Fact[i][2] eq 6) and (Degree(Fact[i][1]) eq 1) then
            num_sext := num_sext + 1;
        end if;
    end for;

    return num_sext;
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
set_cube_flag(p,f): wrapper for has_cube_val(p,f,cubes), converting true/false into 1/0

INPUTS: p
	- p is a prime
	- f is a binary sextic form f(x,z) over Fp.
    - cubes is the list of cubes mod p

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
set_affine_cube_flag(p,f): wrapper for has_affine_cube_val(p,f, cubes), converting 
                            true/false into 1/0

INPUTS: p
    - p is a prime
    - f is a binary sextic form f(x,z) over Fp.
    - cubes is the list of cubes mod p

OUTPUT: returns 1 if f(x,z) takes a nonzero cubic residue value,
        returns 0 if f(x,z) doesn't take a nonzero cubic residue value
*/
set_affine_cube_flag := function(p,f,cubes)
    if has_affine_cube_val(p,f,cubes) then
        return 1;
    end if;

    return 0;
end function;

/*
set_root_flag(p,f): wrapper for has_simple_root(p,f), converting true/false into 1/0

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

// TODO: UPDATE W/ EXACT VALUES, WHEN APPROPRIATE!

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
    - file_out is a file to collect data

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


count_sextic_forms := procedure(p, c0, file_out)

    R<x,z> := PolynomialRing(GF(p), 2);
    cubes, noncube := setup(p);

    // Compute lifting probabilities

    // nu - for lifting double roots
    nu := (3*p^4 - p^3 + p^2 - 3*p + 6)/(6*p^5);

    // pi - for lifting triple roots
    if p eq 7 then
        pi := 17694619/141229221;
    else
        pi := (3*p^6 + 3*p^4 + 3*p^3 + p^2 + 1)/(3*(p^4 + p^3 + p^2 + p + 1)*p^3);
    end if;

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

    // double roots
    count_double := 0;
    count_double2 := 0;
    count_double3 := 0;
    count_star_double := 0;
    count_star_double2 := 0;
    count_star_double3 := 0;
    count_case1_double := 0;
    count_case1_double2 := 0;
    count_case1_double3 := 0;
    count_star1_double := 0;
    count_star1_double2 := 0;
    count_star1_double3 := 0;

    // triple roots
    count_triple := 0;
    count_triple2 := 0;
    count_star_triple := 0;
    count_star_triple2 := 0;
    count_case1_triple := 0;
    count_case1_triple2 := 0;
    count_star1_triple := 0;
    count_star1_triple2 := 0;

    // sextuple root
    count_sext := 0;
    count_star_sext := 0;
    count_case1_sext := 0;
    count_star1_sext := 0;

    // insoluble
    count_insoluble := 0;
    count_star_insoluble := 0;
    count_case1_insoluble := 0;
    count_star1_insoluble := 0;

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
    
                        // check for double/triple roots
                        if f eq 0 then

                        elif (cube_flag + root_flag) eq 0 then    // no cube/simple roots

                            num_double := count_double_roots(p,f);
                            num_triple := count_triple_roots(p,f);
                            num_sext   := count_sext_roots(p,f);

                            // neither double nor triple roots
                            if (num_double + num_triple + num_sext) eq 0 then
                                // print "insoluble -", f; // optional printing
                                count_insoluble := count_insoluble + 1;
                                count_star_insoluble := count_star_insoluble + star_flag;
                                count_case1_insoluble := count_case1_insoluble + case1_flag;
                                count_star1_insoluble := count_star1_insoluble + case1_flag*star_flag;

                            // f has one double root, no other root    
                            elif num_double eq 1 then  
                                // print "double root -",f; // optional printing
                                count_double := count_double + 1;
                                count_star_double := count_star_double + star_flag;
                                count_case1_double := count_case1_double + case1_flag;
                                count_star1_double := count_star1_double + case1_flag*star_flag;

                            // f has two double roots, no other root    
                            elif num_double eq 2 then  
                                // print "2 double root -",f; // optional printing
                                count_double2 := count_double2 + 1;
                                count_star_double2 := count_star_double2 + star_flag;
                                count_case1_double2 := count_case1_double2 + case1_flag;
                                count_star1_double2 := count_star1_double2 + case1_flag*star_flag;

                            // f has three double roots, no other root    
                            elif num_double eq 3 then  
                                // print "3 double root -",f; // optional printing
                                count_double3 := count_double3 + 1;
                                count_star_double3 := count_star_double3 + star_flag;
                                count_case1_double3 := count_case1_double3 + case1_flag;
                                count_star1_double3 := count_star1_double3 + star_flag*case1_flag;

                            // f has one triple root, no other root    
                            elif num_triple eq 1 then  
                                // print "triple root -",f; // optional printing
                                count_triple := count_triple + 1;
                                count_star_triple := count_star_triple + star_flag;
                                count_case1_triple := count_case1_triple + case1_flag;
                                count_star1_triple := count_star1_triple + star_flag*case1_flag;

                            // f has two triple roots, no other root
                            elif num_triple eq 2 then 
                                // print "2 triple root -", f; // optional printing
                                count_triple2 := count_triple2 + 1;
                                count_star_triple2 := count_star_triple2 + star_flag;
                                count_case1_triple2 := count_case1_triple2 + case1_flag;
                                count_star1_triple2 := count_star1_triple2 + star_flag*case1_flag;

                            // f has a sextuple root
                            else
                                // print "sextuple root -", f; // optional printing
                                count_sext := count_sext + 1;
                                count_star_sext := count_star_sext + star_flag;
                                count_case1_sext := count_case1_sext + case1_flag;
                                count_star1_sext := count_star1_sext + star_flag*case1_flag;
                           
                            end if;
                        end if;

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

                        // check for double/triple roots
                        if (cube_flag + root_flag) eq 0 then    // no cube/simple roots

                            num_double := count_double_roots(p,f);
                            num_triple := count_triple_roots(p,f);
                            num_sext   := count_sext_roots(p,f);

                            // neither double nor triple roots
                            if (num_double + num_triple + num_sext) eq 0 then
                                // print "insoluble -", f; // optional printing
                                count_insoluble := count_insoluble + ((p-1)/3);
                                count_star_insoluble := count_star_insoluble + star_flag*((p-1)/3);
                                count_case1_insoluble := count_case1_insoluble + case1_flag*((p-1)/3);
                                count_star1_insoluble := count_star1_insoluble + star_flag*case1_flag*((p-1)/3);

                            // f has one double root, no other root    
                            elif num_double eq 1 then  
                                // print "double root -",f; // optional printing
                                count_double := count_double + ((p-1)/3);
                                count_star_double := count_star_double + star_flag*((p-1)/3);
                                count_case1_double := count_case1_double + case1_flag*((p-1)/3);
                                count_star1_double := count_star1_double + star_flag*case1_flag*((p-1)/3);

                            // f has two double roots, no other root    
                            elif num_double eq 2 then  
                                // print "2 double root -",f; // optional printing
                                count_double2 := count_double2 + ((p-1)/3);
                                count_star_double2 := count_star_double2 + star_flag*((p-1)/3);
                                count_case1_double2 := count_case1_double2 + case1_flag*((p-1)/3);
                                count_star1_double2 := count_star1_double2 + star_flag*case1_flag*((p-1)/3);

                            // f has three double roots, no other root    
                            elif num_double eq 3 then  
                                // print "3 double root -",f; // optional printing
                                count_double3 := count_double3 + ((p-1)/3);
                                count_star_double3 := count_star_double3 + star_flag*((p-1)/3);
                                count_case1_double3 := count_case1_double3 + case1_flag*((p-1)/3);
                                count_star1_double3 := count_star1_double3 + star_flag*case1_flag*((p-1)/3);

                            // f has one triple root, no other root    
                            elif num_triple eq 1 then  
                                // print "triple root -",f; // optional printing
                                count_triple := count_triple + ((p-1)/3);
                                count_star_triple := count_star_triple + star_flag*((p-1)/3);
                                count_case1_triple := count_case1_triple + case1_flag*((p-1)/3);
                                count_star1_triple := count_star1_triple + star_flag*case1_flag*((p-1)/3);

                            // f has two triple roots, no other root
                            elif num_triple eq 2 then 
                                // print "2 triple root -", f; // optional printing
                                count_triple2 := count_triple2 + ((p-1)/3);
                                count_star_triple2 := count_star_triple2 + star_flag*((p-1)/3);
                                count_case1_triple2 := count_case1_triple2 + case1_flag*((p-1)/3);
                                count_star1_triple2 := count_star1_triple2 + star_flag*case1_flag*((p-1)/3);

                            // f has a sextuple root
                            else
                                // print "sextuple root -", f; // optional printing
                                count_sext := count_sext + ((p-1)/3);
                                count_star_sext := count_star_sext + star_flag*((p-1)/3);
                                count_case1_sext := count_case1_sext + case1_flag*((p-1)/3);
                                count_star1_sext := count_star1_sext + star_flag*case1_flag*((p-1)/3);
                           
                            end if;
                        end if;

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

                        // check for double/triple roots
                        if (cube_flag + root_flag) eq 0 then    // no cube/simple roots

                            num_double := count_double_roots(p,f);
                            num_triple := count_triple_roots(p,f);
                            num_sext   := count_sext_roots(p,f);

                            // neither double nor triple roots
                            if (num_double + num_triple + num_sext) eq 0 then
                                // print "insoluble -", f; // optional printing
                                count_insoluble := count_insoluble + ((p-1)/3);
                                count_star_insoluble := count_star_insoluble + star_flag*((p-1)/3);
                                count_case1_insoluble := count_case1_insoluble + case1_flag*((p-1)/3);
                                count_star1_insoluble := count_star1_insoluble + star_flag*case1_flag*((p-1)/3);

                            // f has one double root, no other root    
                            elif num_double eq 1 then  
                                // print "double root -",f; // optional printing
                                count_double := count_double + ((p-1)/3);
                                count_star_double := count_star_double + star_flag*((p-1)/3);
                                count_case1_double := count_case1_double + case1_flag*((p-1)/3);
                                count_star1_double := count_star1_double + star_flag*case1_flag*((p-1)/3);

                            // f has two double roots, no other root    
                            elif num_double eq 2 then  
                                // print "2 double root -",f; // optional printing
                                count_double2 := count_double2 + ((p-1)/3);
                                count_star_double2 := count_star_double2 + star_flag*((p-1)/3);
                                count_case1_double2 := count_case1_double2 + case1_flag*((p-1)/3);
                                count_star1_double2 := count_star1_double2 + star_flag*case1_flag*((p-1)/3);

                            // f has three double roots, no other root    
                            elif num_double eq 3 then  
                                // print "3 double root -",f; // optional printing
                                count_double3 := count_double3 + ((p-1)/3);
                                count_star_double3 := count_star_double3 + star_flag*((p-1)/3);
                                count_case1_double3 := count_case1_double3 + case1_flag*((p-1)/3);
                                count_star1_double3 := count_star1_double3 + star_flag*case1_flag*((p-1)/3);

                            // f has one triple root, no other root    
                            elif num_triple eq 1 then  
                                // print "triple root -",f; // optional printing
                                count_triple := count_triple + ((p-1)/3);
                                count_star_triple := count_star_triple + star_flag*((p-1)/3);
                                count_case1_triple := count_case1_triple + case1_flag*((p-1)/3);
                                count_star1_triple := count_star1_triple + star_flag*case1_flag*((p-1)/3);

                            // f has two triple roots, no other root
                            elif num_triple eq 2 then 
                                // print "2 triple root -", f; // optional printing
                                count_triple2 := count_triple2 + ((p-1)/3);
                                count_star_triple2 := count_star_triple2 + star_flag*((p-1)/3);
                                count_case1_triple2 := count_case1_triple2 + case1_flag*((p-1)/3);
                                count_star1_triple2 := count_star1_triple2 + star_flag*case1_flag*((p-1)/3);

                            // f has a sextuple root
                            else
                                // print "sextuple root -", f; // optional printing
                                count_sext := count_sext + ((p-1)/3);
                                count_star_sext := count_star_sext + star_flag*((p-1)/3);
                                count_case1_sext := count_case1_sext + case1_flag*((p-1)/3);
                                count_star1_sext := count_star1_sext + star_flag*case1_flag*((p-1)/3);
                           
                            end if;
                        end if;

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

                        // check for double/triple roots
                        if (cube_flag + root_flag) eq 0 then    // no cube/simple roots

                            num_double := count_double_roots(p,f);
                            num_triple := count_triple_roots(p,f);
                            num_sext   := count_sext_roots(p,f);

                            // neither double nor triple roots
                            if (num_double + num_triple + num_sext) eq 0 then
                                // print "insoluble -", f; // optional printing
                                count_insoluble := count_insoluble + ((p-1)/3);
                                count_star_insoluble := count_star_insoluble + star_flag*((p-1)/3);
                                count_case1_insoluble := count_case1_insoluble + case1_flag*((p-1)/3);
                                count_star1_insoluble := count_star1_insoluble + star_flag*case1_flag*((p-1)/3);

                            // f has one double root, no other root    
                            elif num_double eq 1 then  
                                // print "double root -",f; // optional printing
                                count_double := count_double + ((p-1)/3);
                                count_star_double := count_star_double + star_flag*((p-1)/3);
                                count_case1_double := count_case1_double + case1_flag*((p-1)/3);
                                count_star1_double := count_star1_double + star_flag*case1_flag*((p-1)/3);

                            // f has two double roots, no other root    
                            elif num_double eq 2 then  
                                // print "2 double root -",f; // optional printing
                                count_double2 := count_double2 + ((p-1)/3);
                                count_star_double2 := count_star_double2 + star_flag*((p-1)/3);
                                count_case1_double2 := count_case1_double2 + case1_flag*((p-1)/3);
                                count_star1_double2 := count_star1_double2 + star_flag*case1_flag*((p-1)/3);

                            // f has three double roots, no other root    
                            elif num_double eq 3 then  
                                // print "3 double root -",f; // optional printing
                                count_double3 := count_double3 + ((p-1)/3);
                                count_star_double3 := count_star_double3 + star_flag*((p-1)/3);
                                count_case1_double3 := count_case1_double3 + case1_flag*((p-1)/3);
                                count_star1_double3 := count_star1_double3 + star_flag*case1_flag*((p-1)/3);

                            // f has one triple root, no other root    
                            elif num_triple eq 1 then  
                                // print "triple root -",f; // optional printing
                                count_triple := count_triple + ((p-1)/3);
                                count_star_triple := count_star_triple + star_flag*((p-1)/3);
                                count_case1_triple := count_case1_triple + case1_flag*((p-1)/3);
                                count_star1_triple := count_star1_triple + star_flag*case1_flag*((p-1)/3);

                            // f has two triple roots, no other root
                            elif num_triple eq 2 then 
                                // print "2 triple root -", f; // optional printing
                                count_triple2 := count_triple2 + ((p-1)/3);
                                count_star_triple2 := count_star_triple2 + star_flag*((p-1)/3);
                                count_case1_triple2 := count_case1_triple2 + case1_flag*((p-1)/3);
                                count_star1_triple2 := count_star1_triple2 + star_flag*case1_flag*((p-1)/3);

                            // f has a sextuple root
                            else
                                // print "sextuple root -", f; // optional printing
                                count_sext := count_sext + ((p-1)/3);
                                count_star_sext := count_star_sext + star_flag*((p-1)/3);
                                count_case1_sext := count_case1_sext + case1_flag*((p-1)/3);
                                count_star1_sext := count_star1_sext + star_flag*case1_flag*((p-1)/3);
                           
                            end if;
                        end if;
                    end for;
                end for;
            end for;
        end for;
    end for;


    // total hensel liftable
    count_hensel := count_cube + count_root - count_both;
    count_star_hensel := count_star_cube + count_star_root - count_star_both;
    count_case1_hensel := count_case1_cube + count_case1_root - count_case1_both;
    count_star1_hensel := count_star1_cube + count_star1_root - count_star1_both;

    print "p =", p, "c0 =", c0;
    print "type, total, star, case1, star1";
    print "total:", total, total_star, total_case1, total_star1;
    print "cube:", count_cube, count_star_cube, count_case1_cube, count_star1_cube;
    print "root:", count_root, count_star_root, count_case1_root, count_star1_root;
    print "both:", count_both, count_star_both, count_case1_both, count_star1_both;
    print "hensel:", count_hensel, count_star_hensel, count_case1_hensel, count_star1_hensel;
    print "insoluble:", count_insoluble, count_star_insoluble, count_case1_insoluble, count_star1_insoluble;
    print "double:", count_double, count_star_double, count_case1_double, count_star1_double;
    print "double2:", count_double2, count_star_double2, count_case1_double2, count_star1_double2;
    print "double3:", count_double3, count_star_double3, count_case1_double3, count_star1_double3;
    print "triple:", count_triple, count_star_triple, count_case1_triple, count_star1_triple;
    print "triple2:", count_triple2, count_star_triple2, count_case1_triple2, count_star1_triple2;
    print "sextuple:", count_sext, count_star_sext, count_case1_sext, count_star1_sext;

    PrintFile(file_out, [c0, total, count_hensel, count_insoluble, count_double, count_double2, count_double3, count_triple, count_triple2, count_sext, total_star, count_star_hensel, count_star_insoluble, count_star_double, count_star_double2, count_star_double3, count_star_triple, count_star_triple2, count_star_sext, total_case1, count_case1_hensel, count_case1_insoluble, count_case1_double, count_case1_double2, count_case1_double3, count_case1_triple, count_case1_triple2, count_case1_sext, total_star1, count_star1_hensel, count_star1_insoluble, count_star1_double, count_star1_double2, count_star1_double3, count_star1_triple, count_star1_triple2, count_star1_sext]);

end procedure;

/*
count_cubic_forms(p): procedure to count the number of cubic forms f(x,z) with nonzero leading
                        coeff which possess an Fp-point liftable to a Qp-point by Hensel's lemma. 
                        In the case where f(x,z) has only multiple roots and takes no cube values, 
                        we compute the probability of the root lifting, resulting in a computation
                        of rho_3,3^aff.

INPUTS: p
        - p is a prime

PRINTED VALUES:
        - total:            total number of bin cubic forms mod p
        - total_hensel:     total with a hensel-liftable point (cube val or simple root)
        - count_double:     number of forms with only a double root
        - count_double2:    number of forms with only two double roots
        - count_double3:    number of forms with only three double roots
        - count_triple:     number of forms with only a triple root
        - count_triple2:    number of forms with only two triple roots
        - count_insoluble:  number of forms which are insoluble (0 for p >> 0)
        - rho33aff:         probability of such a binary cubic having an affine point
*/
count_cubic_forms := procedure(p)

    R<x,z> := PolynomialRing(GF(p), 2);
    cubes, noncube := setup(p);

    // Initialize all counters

    // totals
    total := 0;
    count_cube := 0;
    count_root := 0;
    count_both := 0;
    count_insoluble := 0;
    count_double := 0;
    count_triple := 0;

    // flags
    root_flag := 0;
    cube_flag := 0;

    // iterate over all forms c3x^3 + ... + c0z^3 with 0 < c3 < p
    for c0 in [0 .. p-1] do
        for c1 in [0 .. p-1] do
            for c2 in [0 .. p-1] do
                for c3 in [1 .. p-1] do

                    f := c3*x^3 + c2*x^2*z + c1*x*z^2 + c0*z^3;

                    // check for cube values and simple roots
                    cube_flag := set_affine_cube_flag(p,f, cubes);
                    root_flag := set_root_flag(p,f);

                    total := total + 1;
                    count_cube := count_cube + cube_flag;
                    count_root := count_root + root_flag;
                    count_both := count_both + cube_flag*root_flag;

                    // if neither cube or root, check for double roots
                    if (cube_flag + root_flag) eq 0 then

                        num_double := count_double_roots(p,f);
                        num_triple := count_triple_roots(p,f);

                        // neither double nor triple roots
                        if (num_double + num_triple) eq 0 then
                            print "insoluble -", f; // optional printing
                            count_insoluble := count_insoluble + 1;

                        // f has one double root, no other root    
                        elif num_double eq 1 then  
                            // print "double root -",f; // optional printing
                            count_double := count_double + 1;

                        // f has one triple root, no other root
                        else
                            // print "triple root -", f; // optional printing
                            count_triple := count_triple + 1;
                        end if;
                    end if;

                end for;
            end for;
        end for;
    end for;

    print "";
    print "p =", p;
    print "total", total;
    //print "cube", count_cube;
    //print "root", count_root;
    //print "both", count_both;
    total_hensel := count_cube + count_root - count_both;
    print "hensel", total_hensel;
    print "insoluble", count_insoluble;
    print "double root", count_double;
    print "triple root", count_triple;
    print "";

    // computing rho33aff
    alpha := (p^3 + p + 1)/(p^4 + p^3 + p^2 + p + 1);
    rho33aff := (total_hensel + count_triple*alpha)/total;
    print "rho33aff =", rho33aff;

    // computing pi
    pi := 1/p - 1/p^2 + rho33aff/p^3;
    print "pi =", pi;

end procedure;

/*
count_quartic_forms(p): procedure to count the number of quartic forms f(x,z) with nonzero leading
                        coeff which possess an Fp-point liftable to a Qp-point by Hensel's lemma. 
                        In the case where f(x,z) has only multiple roots and takes no cube values, 
                        we compute the probability of the root lifting, resulting in a computation
                        of rho_3,4^aff.

INPUTS: p
        - p is a prime

PRINTED VALUES:
        - total:            total number of bin cubic forms mod p
        - total_hensel:     total with a hensel-liftable point (cube val or simple root)
        - count_double:     number of forms with only a double root
        - count_double2:    number of forms with only two double roots
        - count_double3:    number of forms with only three double roots
        - count_triple:     number of forms with only a triple root
        - count_triple2:    number of forms with only two triple roots
        - count_insoluble:  number of forms which are insoluble (0 for p >> 0)
        - rho34aff:         probability of such a binary cubic having an affine point
*/
count_quartic_forms := procedure(p)

    R<x,z> := PolynomialRing(GF(p), 2);
    cubes, noncube := setup(p);

    // Initialize all counters

    // totals
    total := 0;
    count_cube := 0;
    count_root := 0;
    count_both := 0;
    count_insoluble := 0;
    count_double := 0;
    count_double2 := 0;
    count_triple := 0;

    // flags
    root_flag := 0;
    cube_flag := 0;

    // iterate over all forms c4x^4 + ... + c0z^3 with 0 < c4 < p
    for c0 in [0 .. p-1] do
        for c1 in [0 .. p-1] do
            for c2 in [0 .. p-1] do
                for c3 in [0 .. p-1] do
                    for c4 in [1 .. p-1] do

                        f := c4*x^4 + c3*x^3*z + c2*x^2*z^2 + c1*x*z^3 + c0*z^4;

                        // check for cube values and simple roots
                        cube_flag := set_affine_cube_flag(p,f, cubes);
                        root_flag := set_root_flag(p,f);

                        total := total + 1;
                        count_cube := count_cube + cube_flag;
                        count_root := count_root + root_flag;
                        count_both := count_both + cube_flag*root_flag;
        
                        // if neither cube or root, check for double/triple roots
                        if (cube_flag + root_flag) eq 0 then

                            num_double := count_double_roots(p,f);
                            num_triple := count_triple_roots(p,f);

                            // neither double nor triple roots
                            if (num_double + num_triple) eq 0 then
                                //print "insoluble -", f; // optional printing
                                count_insoluble := count_insoluble + 1;

                            // f has one double root, no other root    
                            elif num_double eq 1 then  
                                // print "double root -",f; // optional printing
                                count_double := count_double + 1;

                            // f has two double roots, no other root    
                            elif num_double eq 2 then  
                                // print "2 double root -",f; // optional printing
                                count_double2 := count_double2 + 1;

                            // f has one triple root, no other root
                            else
                                // print "triple root -", f; // optional printing
                                count_triple := count_triple + 1;
                            end if;
                        end if;

                    end for;
                end for;
            end for;
        end for;
    end for;

    print "";
    print "p =", p;
    print "total", total;
    //print "cube", count_cube;
    //print "root", count_root;
    //print "both", count_both;
    total_hensel := count_cube + count_root - count_both;
    print "hensel", total_hensel;
    print "insoluble", count_insoluble;
    print "double root", count_double;
    print "2 double root", count_double2;
    print "triple root", count_triple;
    print "";

    // computing rho34aff
    nu := (3*p^4 - p^3 + p^2 - 3*p + 6)/(6*p^5);
    rho34aff := (total_hensel + count_double*nu + count_double2*(1-(1-nu)^2))/total;
    print "rho34aff =", rho34aff;

end procedure;