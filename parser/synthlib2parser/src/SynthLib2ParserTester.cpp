/*
  Copyright (c) 2013,
  Abhishek Udupa,
  Mukund Raghothaman,
  The University of Pennsylvania

  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions are
  met:

  1. Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

  2. Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

  3. Neither the name of the copyright holder nor the names of its
  contributors may be used to endorse or promote products derived from
  this software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
  HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

#include <SynthLib2ParserIFace.hpp>

#include <sstream>

using namespace SynthLib2Parser;


FunTerm* flatten(FunTerm* f) {

  const std::string& fname = f->GetFunName();
  if(fname != "and" && fname != "or") {
    return f;
  }

  auto args = f->GetArgs();
  std::vector<Term*> new_args;
  for(auto x : args) {
    FunTerm* n_x = flatten( dynamic_cast<FunTerm*>(x) );
    if(n_x->GetFunName() == fname) {
      for(auto y : n_x->GetArgs()) new_args.push_back(y);
    }
    else {
      new_args.push_back(n_x);
    }
  }

  return new FunTerm( f->GetLocation(), fname, new_args);
}


FunTerm* do_negation(FunTerm* f) {
  const std::string& fname = f->GetFunName();

  if(fname == "and" || fname == "or") {
    // dont care memory leak

    auto args = f->GetArgs();
    std::vector<Term*> new_args;
    for(auto x : args) {
      new_args.push_back( do_negation(dynamic_cast<FunTerm*>(x)) );
    }

    if(fname == "and") {
      return new FunTerm(f->GetLocation(), "or", new_args);
    }
    else{
      return new FunTerm(f->GetLocation(), "and", new_args);
    }
   
  }
  else if(fname == "not") {
    return  dynamic_cast<FunTerm*>( f->GetArgs()[0] );
  }

  const std::map<string,string> negate_map = {
    {">" , "<="},
    {">=", "<"},
    {"<" , ">="},
    {"<=", ">"},
    {"!=", "="},
    {"=", "!="}
  };

  auto it = negate_map.find(fname); 
  if(it != negate_map.end() ){
    auto args = f->GetArgs();
    return new FunTerm(f->GetLocation(), it->second, args);
  }
  else {
    std::cout << __FILE__ <<":" << __LINE__ << "Error: unhandled negate operation: "
	      << fname << std::endl;    
  }

  return f;
}




FunTerm* reduce_not(FunTerm* f) {
  const std::string& fname = f->GetFunName();
  auto args = f->GetArgs();

  //std::cout << __FILE__ <<":" << __LINE__ << "fname:"  << fname << std::endl;

  if(fname == "not") {

    //std::cout << __FILE__ <<":" << __LINE__ << "in not branch" << std::endl;

    if(args.size()!=1) {
      std::cout << __FILE__ <<":" << __LINE__ << "Error: (not) should have exactly one arg\n";
    }
    return do_negation( dynamic_cast<FunTerm*> (args[0]) );
  }
  else if(fname == "or" || fname == "and") {

    std::vector<Term*> new_args;
  
    for(auto x : args) {
      auto r_x = reduce_not( dynamic_cast<FunTerm*> (x) );
      new_args.push_back( r_x );
    }

    return new FunTerm(f->GetLocation(), fname, new_args);
  }

  return f;
}



FunTerm* flip(FunTerm* f) {

  const std::map<string,string> flip_map = {
    {">" , "<"},
    {">=", "<="},
    {"<" , ">"},
    {"<=", ">="},
    {"=", "="},
  };

  const std::string& fname = f->GetFunName();

  auto it = flip_map.find(fname); 
  if(it != flip_map.end() ){
    auto args = f->GetArgs();
    std::swap(args[0], args[1]);
    return new FunTerm(f->GetLocation(), it->second, args);
  }

  return f;
}



bool cond_match(FunTerm* A, FunTerm* B, bool try_flip) {
  std::ostringstream sa;
  std::ostringstream sb;
  
  sa << *A;
  sb << *B;
  if(sa.str() == sb.str()) {
    return true;
  }

  if(try_flip) {
    FunTerm* nA = flip(A);
    return cond_match(nA, B, false);
  }

  return false;
}


std::vector<FunTerm*> extract(FunTerm* f) {
  const std::string& fname = f->GetFunName();

  std::vector<FunTerm*> res;
  
  if(fname == "and") {
    for(auto* arg : f->GetArgs()) {
      FunTerm* tm =  dynamic_cast<FunTerm*> (arg);
      for(auto* x : extract(tm)) {
	res.push_back(x);
      }
    }
  }
  else{
    res.push_back(f);
  }

  return res;
}

void extract_all(FunTerm* f,
		 std::vector<FunTerm*>& cond,
		 std::vector<FunTerm*>& assgn,
		 std::vector<FunTerm*>& havoc ) {

  std::vector<FunTerm*> terms = extract(f);
  for (auto* t : terms) {
    const string& name = t->GetFunName();
    auto args = t->GetArgs();
    if(name == ">" || name == "<" || name == "<=" || name == ">=" || name == "!=") {

      // std::cout << " compare operations ... " << std::endl;
      cond.push_back(t);
    }
    else if(name == "=") {
      //assgn.push_back(t);

      // std::cout << " equal or assign operations ... " << std::endl;
      // std::cout << "#args: " << args.size() << std::endl;
      // std::cout << "arg[0] : " << *(args[0]) << std::endl; 
      // std::cout << "arg[1] : " << *(args[1]) << std::endl;

      std::ostringstream oss;
      oss << *(args[0]);
      std::string var_name = oss.str();
      int len  = var_name.length();
      if(var_name[len-1] == '!') {
	assgn.push_back(t);
      } else {
	cond.push_back(t);
      }

      // std::cout << "equal or assign is done " << std::endl ; 
    }
    else if(name == "or") {
      havoc.push_back(t);
    }
    else {
      std::cout << __FILE__ << ":" << __LINE__ << "unknown operation in loop:"
		<< name << std::endl; 
    }
  }

}


FunTerm* remove_sub(FunTerm*f, FunTerm* sub) {
  const std::string & fname = f->GetFunName();
  auto args = f->GetArgs();
  std::vector<Term*> new_args;
  for(auto x : args) {
    if( cond_match( dynamic_cast<FunTerm*>(x), sub, true) ) {
      continue;
    }
    new_args.push_back(x);
  }

  return new FunTerm(f->GetLocation(), fname, new_args);
}



FunTerm* simplify_or(FunTerm* f) {
  const std::string & fname = f->GetFunName();
  if(fname != "or") {
    return f;
  }


  auto args = f->GetArgs();

  // std::cout << "simplifying or ... args: " << args.size() << std::endl;

      
  if(args.size() != 2) {
    std::cout << __FILE__ << ":" << __LINE__
	      << "assume (or) has two operands\n";

    std::cout << " ============= \n";
    std::cout << *f << std::endl;
    std::cout << " ============= \n";
    
  }

  FunTerm* left = dynamic_cast<FunTerm*> (args[0]);
  FunTerm* right = dynamic_cast<FunTerm*> (args[1]);
  
  std::vector<FunTerm*> conds_left;
  std::vector<FunTerm*> conds_right;
  std::vector<FunTerm*> tmp;
  

  // std::cout << "will extract from left/right" << std::endl;
  
  extract_all(left, conds_left, tmp, tmp);
  // std::cout << "left: " << conds_left.size() << std::endl;

  extract_all(right, conds_right, tmp, tmp);

  // std::cout << "right: " << conds_right.size() << std::endl;

  std::vector<FunTerm*> m;
  for(auto x : conds_left) {
    for(auto y : conds_right) {
      if(cond_match(x,y, true)) {
	m.push_back(x);
	break;
      }
    }
  }

  std::cout << "common conditions: " << m.size() << std::endl;

  for(auto x : m) {
    left = remove_sub(left, x);
    right = remove_sub(right, x);
  }

  //std::vector<Term*> tms = {left, right};
  FunTerm* new_or = new FunTerm(f->GetLocation(), "or", {left, right});

  std::vector<Term*> tms (m.begin(), m.end());
  tms.push_back(new_or);

  return new FunTerm(f->GetLocation(), "and", tms);  
}


std::vector<FunTerm*> detect_loop_condition(FunTerm* loop, FunTerm* post) {

  // pattern:
  //  inv-f  (and p ... )
  //  post-f (or p ...)

  std::vector<FunTerm*> cond_loop;
  std::vector<FunTerm*> tmp;
  extract_all(loop, cond_loop, tmp, tmp);

  /*
  std::set<std::string> cond_strs;
  for(auto c : cond_loop) {
    std::ostringstream oss;
    oss << *c;
    cond_strs.insert( oss.str() );
  }
  */
  
  auto args = post->GetArgs();

  //std::vector<std::string> m;
  std::vector<FunTerm*> m;
  
  for(auto x : args) {
    for(auto y : cond_loop) {
      if( cond_match( dynamic_cast<FunTerm*>(x),y,true) ) {
	//std::ostringstream oss;
	//oss << *x;
	//m.push_back( oss.str() );
	m.push_back(y);
	break;
      }
    }
  }


  // remove matched ones
  for(auto y: m) {
    remove_sub(loop, y);
    remove_sub(post, y);
  }
  
  // std::cout << "loop cond match: " << m.size() << "\n";

  return m;
}


bool is_havoc(FunTerm* f) {
  if( f->GetFunName() != "or" ) {
    return false;
  }

  /*
  auto args = f->GetArgs();
  if(args.size() != 2) {
    std::cout << __FILE__ << ":" << __LINE__ <<
	      << "OR is expected to have exactly two args: "
	      << args.size() << std::endl;
  }

  std::vector<FuncTerm*> cond0;
  std::vector<FuncTerm*> cond1
  std::vector<FuncTerm*> dontcare;

  extract_all( dynamic_cast<FuncTerm*>( args[0] ), cond0, dontcare, dontcare);
  extract_all( dynamic_cast<FuncTerm*>( args[1] ), cond1, dontcare, dontcare);
  */

  return true;
}




std::string handle_pre(FunTerm* f) {

  std::ostringstream os;

  const std::string op_name = f->GetFunName();
  
  if( f->GetFunName() == "and") {
    for(auto* arg : f->GetArgs()) {
      FunTerm* tm =  dynamic_cast<FunTerm*> (arg);
      os << handle_pre(tm);
    }

  }
  else{

    const string& fname = f->GetFunName();


    if(fname == "=") {
      os << *f << ";\n";
    }
    else if(fname == ">" || fname == "<" || fname == "<=" || fname == ">=") {
      os << "assume(" << *f << ");\n";
    }
    else {
      std::cout << __FILE__ << ":" << __LINE__ << ", error: unknown operation "
		<< fname << std::endl;
    }

  }

  return os.str();
}

std::string handle_have(FunTerm*);
std::string handle_body(FunTerm*);
std::string handle_loop(FunTerm*);

std::string handle_havoc (FunTerm* f) {
  return "havoc";

}
std::string handle_body (FunTerm* f) {
  return "body";
}

std::string handle_loop(FunTerm* loop) {
  std::ostringstream os;

  // check if the very first is havoc or not
  if( loop->GetFunName() == "or" ) {
    os << "while (*) {\n";
    


    os << "\n}\n";
  }

  std::vector<FunTerm*> cond;
  std::vector<FunTerm*> assgn;
  std::vector<FunTerm*> havoc; // potential havoc
  

  if(cond.size() > 1) {
    std::cout << "Warn: " << cond.size() << " conditions!" << std::endl;
    for(auto x : cond) std::cout << *x << " | ";
    std::cout << std::endl;
  }

  // process conditions
  if (cond.size() == 1) {
      os << "while( " <<  *(cond[0]) << " ) {\n" ;
  }
  else {
    os << "\n_TODO_conds\n";
  }

  // process assignments
  for(auto* a : assgn) {
    os << *a << "\n";
  }

  // process havoc
  if(havoc.size() > 1) {
    std::cout << "Warn: " << cond.size() << " havocs!" << std::endl;
    for(auto x : cond) std::cout << *x << " | ";
    std::cout << std::endl;
  }

  for(auto* h : havoc) {
    os << handle_loop(h);
  }

  os << "}\n";
  return os.str();
}

std::string handle_post(FunTerm* post) {

  std::vector<FunTerm*> cond;
  std::vector<FunTerm*> assgn;
  std::vector<FunTerm*> havoc; // potential havoc

  //extract_all(post, cond, assgn, havoc);

  
  
  
  return "post";
}



int main(int argc, char* argv[])
{
  SynthLib2Parser::SynthLib2Parser* Parser = new SynthLib2Parser::SynthLib2Parser();
  try {
    (*Parser)(argv[1]);
  } catch (const exception& Ex) {
    cout << Ex.what() << endl;
    exit(1);
  }

  FunTerm* pre;
  FunTerm* loop;
  FunTerm* post;

  auto TheProgram = Parser->GetProgram();
  for (auto cmd : TheProgram->GetCmds()) {
    if (cmd->GetKind() == CMD_FUNDEF) {
      FunDefCmd* fdc = static_cast<FunDefCmd*>(cmd);


      const string fname = fdc->GetFunName();
      FunTerm* tm = dynamic_cast<FunTerm*> (fdc->GetTerm());
      if(fname == "pre-f") {
	pre = tm;
      }
      else if(fname == "trans-f") {
	loop = tm;
      }
      else if(fname == "post-f") {
	post = tm;
      }
      else {
	cout << __FILE__ << ":" << __LINE__ << "Error: got unknown term" << std::endl;
	cout << __FILE__ << ":" << __LINE__ << "fname: " << fname << std::endl;
	cout << __FILE__ << ":" << __LINE__ << "term: " << *tm << std::endl;	    
      }
    }
  }


  bool expected = false;
  if(post->GetFunName() == "or" || post->GetFunName() == "not") {
    expected = true;
  }
  
  if(post->GetFunName() != "or" && post->GetFunName() != "and" && post->GetFunName() != "not"   ) {
    std::vector<Term*> vs;
    vs.push_back(post);
    
    post = new FunTerm( post->GetLocation(), "and", std::move(vs) );
  }

  
  //std::string res = handle_pre(pre);
  //std::cout << res << std::endl;
  //handle_loop( loop );

  // flatten
  //pre = flatten(pre);



  // std::cout << "loop: \n" << *loop << std::endl;

  loop = reduce_not(loop);
  loop = flatten(loop);

  // std::cout << "after reduce_not, flatten:\n" << *loop << std::endl;

  
  if(loop->GetFunName() == "or") {
    loop = simplify_or( loop );
    // std::cout << "after simplify_or:\n"
    // << *loop << std::endl;
  }



  //std::cout <<"before reducing: " << *post << std::endl;
  //FunTerm* p = reduce_not(post);
  //std::cout <<"after reducing: " << *p << std::endl;  
  FunTerm* post_r = reduce_not(post);


  auto res = detect_loop_condition(loop, post_r);

  if(expected && res.size() == 0) {

    if(loop->GetFunName() == "or") {
      std::cout << "expected,but failed to consider (or) in loop. " << std::endl;
    }
    else {
      std::cout << "expected,but failed due to others. " << std::endl;
    }
    
  }

  //handle_post( post );
  
  // cout << (*Parser->GetProgram()) << endl;

  delete Parser;
}
