default Order dec

$include <prelude.sail>
$include <string.sail>

$include "includes/infix_op.sail"

val main : unit -> unit

function main() = {
  print_int("3 <=|=> 3 = ", 3 <=|=> 3)
}
