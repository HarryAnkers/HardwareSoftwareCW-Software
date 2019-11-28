theory HSV_CW_1_4 imports Complex_Main begin

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

(* L numbers *)
fun dirac :: "nat \<Rightarrow> nat" where
  "dirac n = (if n = 0 then 1 else 0)"

theorem dirac_suc: "dirac (Suc n) = 0" 
  apply simp
  done

fun Lnum :: "nat \<Rightarrow> nat" where
  "Lnum n = (if n \<le> 1 then n else 2 + Lnum (n-1))"

value "Lnum 0" (* 0 *)
value "Lnum 1" (* 1 *)
value "Lnum 2" (* 3 *)
value "Lnum 3" (* 5 *)

(* Proving that closed form is equivalent to recursive definition *)
theorem "Lnum n = 2*n+dirac n-1"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc k) 
  assume IH: "Lnum k = 2*k+dirac(k)-1"
  have "Lnum (Suc k) = 2*(Suc k)+dirac(Suc k)-1"
  proof (induct k)
    case 0
    then show ?case by simp
  next
    case (Suc k)
    then show ?case by simp
  qed
  then show ?case by auto
qed

(* Pyr numbers *)
fun pyr :: "nat \<Rightarrow> nat" where
  "pyr n = (if n = 0 then 0 else (n)*(n) + pyr (n-1))"

value "pyr 0" (* 0 *)
value "pyr 1" (* 1 *)
value "pyr 2" (* 5 *)
value "pyr 3" (* 14 *)

find_theorems "_ div ?x + _ div ?x"
thm div_add

(* Proving that closed form is equivalent to recursive definition *)
theorem "pyr n = ((2*n + 1) * (n + 1) * n) div 6"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc k) 
  (* induction hypothesis *)
  assume IH: "pyr k = (2*k + 1) * (k + 1) * k div 6"

  (* the actual proof *)
  have "pyr (Suc k) = (Suc k)*(Suc k) + pyr k"
    by simp
  have "... = (Suc k)*(Suc k) + ((2*k + 1) * (k + 1) * k div 6)"
    using IH by simp
  have "... = (6*(Suc k)*(Suc k) + (2*k + 1) * (k + 1) * k) div 6 "
    by linarith
  have "... = (6*(k+1)*(k+1) + (2*k + 1) * (k + 1) * k) div 6 "
    by (simp add: distrib_right power2_eq_square)
  have "... = (6*(k+1)*(k+1) + (2*k + 1) * (k^2 + k)) div 6"
    by (metis (mono_tags, lifting) Suc_eq_plus1 mult.assoc mult_Suc power2_eq_square semiring_normalization_rules(24))
    have "... = (2*(Suc k) + 1) * ((Suc k) + 1) * (Suc k) div 6"
      by (smt Groups.add_ac(3) Suc_eq_plus1 \<open>(6 * (k + 1) * (k + 1) + (2 * k + 1) * (k + 1) * k) div 6 = (6 * (k + 1) * (k + 1) + (2 * k + 1) * (k\<^sup>2 + k)) div 6\<close> add_Suc_right distrib_right nat_mult_1 numeral_Bit0 numeral_Bit1 numeral_code(1) semiring_normalization_rules(16) semiring_normalization_rules(23))
  show ?case
    using \<open>(6 * (k + 1) * (k + 1) + (2 * k + 1) * (k + 1) * k) div 6 = (6 * (k + 1) * (k + 1) + (2 * k + 1) * (k\<^sup>2 + k)) div 6\<close> \<open>(6 * (k + 1) * (k + 1) + (2 * k + 1) * (k\<^sup>2 + k)) div 6 = (2 * Suc k + 1) * (Suc k + 1) * Suc k div 6\<close> \<open>(6 * Suc k * Suc k + (2 * k + 1) * (k + 1) * k) div 6 = (6 * (k + 1) * (k + 1) + (2 * k + 1) * (k + 1) * k) div 6\<close> \<open>Suc k * Suc k + (2 * k + 1) * (k + 1) * k div 6 = (6 * Suc k * Suc k + (2 * k + 1) * (k + 1) * k) div 6\<close> \<open>Suc k * Suc k + pyr k = Suc k * Suc k + (2 * k + 1) * (k + 1) * k div 6\<close> \<open>pyr (Suc k) = Suc k * Suc k + pyr k\<close> by linarith
qed 
end