\\ psi.gp -- the coefficients (constant term first) of Psi_d for d <= 30, for comparison with the
\\ table `psi` in lean/SpectralAlgebras/Cycles.lean.
read("common.gp");
for(d=1,30, print(d, " ", Vecrev(Psi(d))));
quit;
