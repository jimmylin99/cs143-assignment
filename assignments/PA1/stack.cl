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
   };
};

class PlusCommand inherits StackCommand {
   isNil() : Bool { false };
};

class SwapCommand inherits StackCommand {
   isNil() : Bool { false };
};

class EvaluateCommand inherits StackCommand {
   isNil() : Bool { false };
};

class DisplayCommand inherits StackCommand {
   isNil() : Bool { false };

   exec(s : Stack) : Stack {
      
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
