# List of missed optimisations to look at later

This should be compiled to the identity. But the CSE environment seems to lose
the relationship in the join after the first switch.

   let f x =
     let not_x = if x then false else true in
     if not_x then false else true
