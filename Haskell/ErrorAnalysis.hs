module ErrorAnalysis(ErrorTree, nile, is_nil, cons_et, cons_se, err_prepend, add_to_err, check_surj, check_inj, check_fun', check_fun, 
  check_fun_inj, check_total, check_fun_bij, check_fun_total, check_fun_total_seq, check_fun_total', check_pfun, check_fun_pinj, show_err, check_subseteq, 
  check_seteq, check_relation) where

import Relations
import Sets 
import ShowUtils
import SimpleFuns

data ErrorTree = NilE | Error String [ErrorTree]
    deriving (Eq, Show)
 
-- The 'null' error
nile = NilE

is_nil et = et == NilE 

-- Builds an error with nesting
cons_et s es = Error s es

-- Builds an error without nesting
cons_se s = Error s []

-- Prepends a string to the error string
err_prepend _ NilE = NilE
err_prepend s (Error s' ets) = Error (s++s') ets

add_to_err NilE [] = NilE
add_to_err NilE (e:es) = add_to_err e es
add_to_err (Error s es) es' = (Error s $ es++es')

-- shows the error message
show_errs [] =  ""
show_errs (e:errs) = wr_err (show_err e) ++ (show_errs errs)
    where wr_err es = if null es then "" else "\n\t" ++ es

show_err NilE = ""
show_err (Error s errs) = s ++ show_errs errs

-- Finds error with a surjection 
check_surj f ys = 
    let emsg = "Errors in surjection. The following elements are not mapped to: " in
    if ys `seteq` ran_of f then nile else cons_se $ emsg ++ (showElems' (diff ys $ ran_of f))

-- Finds error with a function
check_fun' msg f =
    let emsg = msg ++ " More than one mapping for the elements: " in
    let xs_monce = find_monces f in
    if functional f then nile else cons_se $ emsg ++ (showElems' xs_monce)

check_fun f = check_fun' "Errors in function." f

-- Finds error with an injection
check_inj f = check_fun' "Errors in injection." (inv f) 

check_fun_bij f xs ys = 
  if fun_bij f xs ys then nile else cons_et "Errors in bijection." [check_fun_total f xs ys, check_inj f, check_surj f ys]

check_fun_inj f xs ys = 
  if fun_inj f xs ys then nile else cons_et "Errors in total injection." [check_fun_total f xs ys, check_inj f]

-- Errors related to totality 
check_total f xs = 
   let es_diff = diff xs (dom_of f) in
   let es_diff2 = diff (dom_of f) xs in
   let errs2 = if null es_diff then nile else cons_se ("No mapping for elements: " ++ (showElems' es_diff)) in
   let errs3 = if null es_diff2 then nile else cons_se ("The following shouldn't be mapped: " ++ (showElems' es_diff2)) in
   if total f xs then nile else cons_et "The totality constraint is unsatisfied. " [errs2, errs3]

-- Errors related to a relation
errs_relation r xs ys = [check_subseteq (dom_of r) xs, check_subseteq (ran_of r) ys]

check_relation r xs ys = 
  if relation r xs ys then nile else cons_et "Errors with domain and range." (errs_relation r xs ys)

-- Errors related to a total function with respect to a set of domain elements
errs_fun_total f xs =
    let err1 = check_total f xs in
    let err2 = check_fun f in
    add_to_err err1 [err2]

check_fun_total' f xs =
   let err = errs_fun_total f xs in
   if fun_total' f xs then nile else err

-- Checking of a total function given a set of domain and range elements
check_fun_total f xs ys =
   let err1 = errs_fun_total f xs in
   let ns_diff = (ran_of f) `diff` ys in
   let errs2 = if ((ran_of f) `subseteq` ys) then nile else cons_se $ "The following are targets but they shouldn't: " ++ (showElems' ns_diff) in
   add_to_err err1 [errs2]

-- Checking of a total function given a set of domain and range elements
check_fun_total_seq f xs ys =
   let err1 = errs_fun_total f xs in
   let ns_diff = (gunion . ran_of $ f) `diff` ys in
   let errs2 = if (null ns_diff) then nile else cons_se $ "The following are targets but they shouldn't: " ++ (showElems' ns_diff) in
   add_to_err err1 [errs2]

check_pfun f xs ys =
    if pfun f xs ys then nile else cons_et "Errors in partial function" $ (errs_relation f xs ys) ++ [check_fun f]

check_fun_pinj f xs ys = 
    if pfun f xs ys then nile else cons_et "Errors in partial injection" $ (errs_relation f xs ys) ++ [check_inj f]

-- Errors related to a subset constraint
check_subseteq r1 r2 =
   if r1 `subseteq` r2 then nile else cons_se $ "The following are not included: " ++ (showElems' $ diff r1 r2)

check_seteq r1 r2 =
    let err1 = check_subseteq r1 r2 in
    let err2 = check_subseteq r1 r2 in
    if r1 `seteq` r2 then nile else cons_et "The sets are unequal." [err1, err2]
