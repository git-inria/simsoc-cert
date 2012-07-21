let (&), (>>), (<<), (--) = Int64.logand, Int64.shift_right_logical, Int32.shift_left, Int64.sub

let get_bits x a b =
  assert (a - b + 1 <= 32);
  Printf.printf "%Ld\n%!" (Int64.of_int32 (1_l << (a - b + 1)) -- 1L);
  Printf.printf "%Ld\n%!" (x );
  (x >> b) & (Int64.of_int32 (1_l << (a - b + 1)) -- 1L)

let _ = 
  let f n = Sys.argv.(n) in
  Printf.printf "%Ld\n%!" 
    (get_bits (Int64.of_string (f 1)) (int_of_string (f 2)) (int_of_string (f 3)))
