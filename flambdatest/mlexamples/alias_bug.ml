
type float_kind_conv =
  | Float_f                        (*  %f | %+f | % f  *)
  | Float_e                        (*  %e | %+e | % e  *)
  | Float_E                        (*  %E | %+E | % E  *)
  | Float_g                        (*  %g | %+g | % g  *)
  | Float_G                        (*  %G | %+G | % G  *)
  | Float_F                        (*  %F | %+F | % F  *)
  | Float_h                        (*  %h | %+h | % h  *)
  | Float_H                        (*  %H | %+H | % H  *)
  | Float_CF                       (*  %#F| %+#F| % #F *)

let char_of_fconv ?(cF='F') fconv = match snd fconv with
  | Float_f -> 'f' | Float_e -> 'e'
  | Float_E -> 'E' | Float_g -> 'g'
  | Float_G -> 'G' | Float_F -> cF
  | Float_h -> 'h' | Float_H -> 'H'
  | Float_CF -> 'F'

let f x = char_of_fconv x

(* let g x = char_of_fconv ~cF:'g' x *)
