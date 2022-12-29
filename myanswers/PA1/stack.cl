(*
 *  CS164 Fall 94
 *
 *  Programming Assignment 1
 *    Implementation of a simple stack machine.
 *
 *  Skeleton file
 *)

class StackCommand {
   isNil() : Bool { true };

   exec(s : Stack) : Stack {
      -- {
      --    (new IO).out_string("c");
      --    s;
      -- }
      s
   };

   toString() : String {
      "Not Implemented"
   };

   toInt() : Int {
      0
   };
};

class PlusCommand inherits StackCommand {
   isNil() : Bool { false };

   toString() : String {
      "+"
   };
};

class SwapCommand inherits StackCommand {
   isNil() : Bool { false };

   toString() : String {
      "s"
   };
};

class EvaluateCommand inherits StackCommand {
   isNil() : Bool { false };

   exec(s : Stack) : Stack {
      {
         let topC : StackCommand <- s.top(),
             sc1 : StackCommand,
             sc2 : StackCommand
         in 
            if topC.toString() = "+" then
               {
                  s <- s.pop();
                  sc1 <- s.top();
                  s <- s.pop();
                  sc2 <- s.top();
                  s <- s.pop();
                  s <- s.push((new IntCommand).init(sc1.toInt() + sc2.toInt()));
               }
            else if topC.toString() = "s" then
               {
                  s <- s.pop();
                  sc1 <- s.top();
                  s <- s.pop();
                  sc2 <- s.top();
                  s <- s.pop();
                  s <- s.push(sc1);
                  s <- s.push(sc2);
               } else 0
            fi fi;
         s;
      }
   };
};

class DisplayCommand inherits StackCommand {
   isNil() : Bool { false };

   exec(s : Stack) : Stack {
      {
         let curS : Stack <- s,
             sc : StackCommand
         in
            while not curS.isEmpty() loop
               {
                  sc <- curS.top();
                  (new IO).out_string(sc.toString().concat("\n"));
                  curS <- curS.pop(); -- fake pop
               }
            pool;
         s;
      }
   };
};

class StopCommand inherits StackCommand {
   isNil() : Bool { false };
};

class IntCommand inherits StackCommand {
   val : Int;

   isNil() : Bool { false };

   init(i : Int) : IntCommand {
      {
         val <- i;
         self;
      }
   };

   toString() : String {
      (new A2I).i2a(val)
   };

   toInt() : Int {
      val
   };
};

class Stack {
   curCommand : StackCommand <- new StackCommand;
   next : Stack;

   init(c : StackCommand, n : Stack) : Stack {
      {
         curCommand <- c;
         next <- n;
         self;
      }
   };

   push(c : StackCommand) : Stack {
      (new Stack).init(c, self)
   };

   pop() : Stack {
      next
   };

   top() : StackCommand {
      curCommand
   };

   isEmpty() : Bool {
      curCommand.isNil()
   };
};

class Main inherits IO {

   main() : Object {
      let isHalt: Bool <- false,
          op: String,
          sc: StackCommand,
          stack: Stack <- new Stack
      in
         while not isHalt loop
         {
            out_string(">");
            op <- in_string();
            if op = "+" then { sc <- new PlusCommand; stack <- stack.push(sc); } else
            if op = "s" then { sc <- new SwapCommand; stack <- stack.push(sc); } else
            if op = "e" then { sc <- new EvaluateCommand; stack <- sc.exec(stack); } else
            if op = "d" then { sc <- new DisplayCommand; sc.exec(stack); } else
            if op = "x" then { sc <- new StopCommand; isHalt <- true; } else
            { 
               sc <- (new IntCommand).init((new A2I).a2i(op)); 
               stack <- stack.push(sc);
            }
            fi fi fi fi fi;
         }
         pool
   };

};
