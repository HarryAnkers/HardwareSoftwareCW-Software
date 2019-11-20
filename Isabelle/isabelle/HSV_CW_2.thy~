theory HSV_CW_2 imports Complex_Main begin
(* Triangle numbers *)
fun triangle :: "nat \<Rightarrow> nat" where
  "triangle n = (if n = 0 then 0 else n + triangle (n-1))"
               
value "triangle 1"
value "triangle 2"
value "triangle 3"

theorem triangle_closed_form: "triangle n = (n+1) * n div 2" 
  apply (induct n)
  apply simp+
  done

(* Tetrahedral numbers *)
fun tet :: "nat \<Rightarrow> nat" where
  "tet n = (if n = 0 then 0 else triangle n + tet (n-1))"

value "tet 1" (* 1 *)
value "tet 2" (* 4 *)
value "tet 3" (* 10 *)
value "tet 4" (* 20 *)
value "tet 5" (* 35 *)
value "tet 6" (* 56 *)

find_theorems "_ div ?x + _ div ?x"
thm div_add

(* Proving that closed form is equivalent to recursive definition *)
theorem "tet n = ((n + 2) * (n + 1) * n) div 6"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc k) 

  (* induction hypothesis *)
  assume IH: "tet k = (k + 2) * (k + 1) * k div 6"

  (* establish a useful fact and label it "*" *)
  have "2 dvd (k + 2) * (k + 1)" by simp
  hence *: "6 dvd (k + 2) * (k + 1) * 3" by presburger

  (* establish another useful fact and label it "**" *)
  have "2 dvd (k + 2) * (k + 1) * k" by simp
  moreover have "3 dvd (k + 2) * (k + 1) * k"
  proof - 
    {
      assume "k mod 3 = 0"
      hence "3 dvd k" by presburger
      hence "3 dvd (k + 2) * (k + 1) * k" by fastforce
    } moreover { 
      assume "k mod 3 = 1"
      hence "3 dvd (k + 2)" by presburger
      hence "3 dvd (k + 2) * (k + 1) * k" by fastforce
    } moreover { 
      assume "k mod 3 = 2"
      hence "3 dvd (k + 1)" by presburger
      hence "3 dvd (k + 2) * (k + 1) * k" by fastforce
    } ultimately
    show "3 dvd (k + 2) * (k + 1) * k" by linarith
  qed
  ultimately have **: "6 dvd (k + 2) * (k + 1) * k" by presburger

  (* the actual proof *)
  have "tet (Suc k) = triangle (Suc k) + tet k" 
    by simp
  also have "... = (k + 2) * (k + 1) div 2 + tet k" 
    using triangle_closed_form by simp
  also have "... = (k + 2) * (k + 1) div 2 + (k + 2) * (k + 1) * k div 6" 
    using IH by simp
  also have "... = ((k + 2) * (k + 1) * 3 + (k + 2) * (k + 1) * k) div 6" 
    using div_add[OF * **] by simp
  also have "... = (k + 2) * (k + 1) * (k + 3) div 6" 
    by (simp add: distrib_left)
  also have "... = (Suc k + 2) * (Suc k + 1) * Suc k div 6"
    by (metis One_nat_def Suc_1 add.commute add_Suc_shift mult.assoc 
        mult.commute numeral_3_eq_3 plus_1_eq_Suc)
  finally show ?case by assumption
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

   (* establish a useful fact and label it "*" *)
  have "1 dvd (k + 1) * (k + 1)" by simp
  hence *: "6 dvd (k + 1) * (k + 1) * 6" by presburger

  (* establish another useful fact and label it "**" *)
  have "2 dvd (2*k + 1) * (k + 1) * k" by simp
  moreover have "3 dvd (2*k + 1) * (k + 1) * k"
  proof - 
    {
      assume "k mod 3 = 0"
      hence "3 dvd k" by presburger
      hence "3 dvd (2*k + 1) * (k + 1) * k" by fastforce
    } moreover { 
      assume "k mod 3 = 1"
      hence "3 dvd (2*k + 1)" by presburger
      hence "3 dvd (2*k + 1) * (k + 1) * k" by fastforce
    } moreover { 
      assume "k mod 3 = 2"
      hence "3 dvd (k + 1)" by presburger
      hence "3 dvd (2*k + 1) * (k + 1) * k" by fastforce
    } ultimately
    show "3 dvd (2*k + 1) * (k + 1) * k" by linarith
  qed
  ultimately have **: "6 dvd (2*k + 1) * (k + 1) * k" by presburger

  (* the actual proof *)
  have "pyr (Suc k) = (Suc k)*(Suc k) + pyr k"
    by simp
  have "... = (Suc k)*(Suc k) + ((2*k + 1) * (k + 1) * k div 6)"
    using IH by simp
  have "... = (6*(Suc k)*(Suc k) + (2*k + 1) * (k + 1) * k) div 6 "
    using div_add[OF * **] by linarith
  have "... = (6*(k+1)*(k+1) + (2*k + 1) * (k + 1) * k) div 6 "
    by (simp add: distrib_right power2_eq_square)
  have "... = (6*(k+1)*(k+1) + (2*k^2 + k) * (k + 1)) div 6" try
    by (smt add_self_div_2 distrib_right mult.assoc mult.commute nonzero_mult_div_cancel_left one_add_one power2_eq_square zero_neq_numeral)
  have "... = (6*k^2+12*k+6 + (2*k^2 + k) * (k + 1)) div 6" try
    by (smt distrib_left_numeral mult.assoc mult.right_neutral numeral_Bit0 one_add_one power2_eq_square power2_sum semiring_normalization_rules(23))
  have "... = (2*(k+1) + 1) * ((k+1) + 1) * (k+1) div 6" try
  finally show ?case by assumption
qed

(* L numbers *)
fun dirac :: "nat \<Rightarrow> nat" where
  "dirac n = (if n = 0 then 1 else 0)"

fun Lnum :: "nat \<Rightarrow> nat" where
  "Lnum n = (if n \<le> 1 then n else 2 + Lnum (n-1))"

value "Lnum 0" (* 0 *)
value "Lnum 1" (* 1 *)
value "Lnum 2" (* 3 *)
value "Lnum 3" (* 5 *)
value "Lnum 4" (* 7 *)
value "Lnum 5" (* 9 *)
value "Lnum 6" (* 11 *)

(* Proving that closed form is equivalent to recursive definition *)
theorem "Lnum n = dirac(n)+(-1+(2*n))"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc k) 
  assume IH: "Lnum k = dirac(k)+(-1+(2*k))"
  have "Lnum (Suc k) = dirac(Suc k)+(-1+(2*(Suc k)))"
  proof (induct k)
    case 0
    then show ?case by simp
  next
    case (Suc k)
    then show ?case by simp
  qed
  then show ?case by auto
qed            

end