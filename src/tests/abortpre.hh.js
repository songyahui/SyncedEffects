"use hiphop"
"use hopscript"

var hh = require( "hiphop" );

hiphop module prg(out O, out S ) {
   loop {
      abort( S.pre ) {
	 emit S();
	 yield;
	 emit O();
      }
      yield;
   }
}


exports.prg = new hh.ReactiveMachine(prg, "abortpre");
