"use hiphop"
"use hopscript"

const hh = require("hiphop")

hiphop module prg( A combine (x, y) => x + y ) {
   fork {
      loop {
	 emit A( 0 );
	 yield;
      }
   } par {
      loop {
	 emit A( 1 );
	 yield;
      }
   } par {
      loop {
	 emit A( 2 );
	 yield;
      }
   }
}

let machine = new hh.ReactiveMachine( prg, "error2" );
