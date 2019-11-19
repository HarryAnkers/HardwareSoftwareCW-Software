theory HSV_CW imports Complex_Main begin
                 
(* We use the following command to search Isabelle's library 
   for theorems that contain a particular pattern. *)
find_theorems "_ \<in> \<rat>"
thm Rats_abs_nat_div_natE

find_theorems "(_ / _)^_"
thm power_divide

(* A proof that the 2*square root of 2 is irrational. *)
theorem sqrt2_irrational_2: "2 * sqrt 2 \<notin> \<rat>"
proof auto
  assume "(2*sqrt 2) \<in> \<rat>"
  then obtain m n where 
    "n \<noteq> 0" and "\<bar>2*sqrt 2\<bar> = real m / real n" and "coprime m n" 
    by (rule Rats_abs_nat_div_natE)
  hence "\<bar>2*sqrt 2\<bar>^2 = (real m / real n)^2" by auto 
  hence "8 = (real m / real n)^2" by simp
  hence "8 = (real m)^2 / (real n)^2" unfolding power_divide by auto
  hence "8 * (real n)^2 = (real m)^2"
    by (simp add: nonzero_eq_divide_eq `n \<noteq> 0`)

  hence "real (8 * n^2) = real(m)^2" by auto
  hence *: "8 * n^2 = m^2"
    using of_nat_power_eq_of_nat_cancel_iff by blast
  hence "even (m^2)" by presburger
  hence "even m" by simp
  then obtain m' where "m = 2 * m'" by auto
  with * have "8 * n^2 = (2 * m')^2" by auto
  hence "8 * n^2 = 4 * m'^2" by simp
  hence *: "2 * n^2 = m'^2" by simp
  hence "even (m'^2)" by presburger
  hence "even m'" by simp
  then obtain m'' where "m' = 2 * m''" by auto
  with * have "2 * n^2 = (2 * m'')^2" by auto
  hence "n^2 = 2 * m''^2" by simp
  hence "n^2 = 2* m''^2" by simp
  hence "even (n^2)" by presburger
  hence "even n" by simp
  with `even m` and `coprime m n` show False by auto
qed



end