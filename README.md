# Density-of-locally-soluble-SECs
This repository includes files related to a joint work with Lea Beneish, "On the density of locally soluble superelliptic curves."

List of files:
- CountForms.m: magma routines for efficiently computing enumerating binary forms f(x,z) over Fp taking a value liftable by Hensel's lemma to a Qp-point of y^3 = f(x,z).
- ComputeSigma1.m: magma file for computing sigma1 and sigma1* exactly, using data from previously running count_sextic_forms(p,c0) from CountForms.m
- CountSexticsEff: an old version of CountForms.m with less functionality. Namely doesn't include relevant computations for rho33aff and rho34aff.
- SEC_lowerbound_examples_28Aug21.ipynb: sage notebook containing calculations and examples of lower bounds for rho_m,d
- SEC_rho36_23Aug21.ipynb: sage notebook containing calculations related to exact formulas for rho_3,6.
