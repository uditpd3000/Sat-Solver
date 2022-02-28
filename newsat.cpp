#include <bits/stdc++.h>
#include <string>
#include <iostream>
#include <vector>

using namespace std;

vector<int> model;     //global variable to store model on which we are currently checking satisfiability

/*
If we assign a proposition some value, then we will remove all the clauses which will get satisfied by this.
Also we will remove the negation of that literal from each clauses.
*/
    
vector<vector<int>> reshape_clauses(int x, vector<vector<int>> clause_list){

        vector<int> removed;   // list of index of clauses which are satisfied and are to be removed from cnf
        int i;
        int n=clause_list.size();
        for(i=0;i<clause_list.size();i++){
            if(binary_search(clause_list[i].begin(),clause_list[i].end(),x)){
                removed.push_back(i);
            }
        }
        int j=0;
        for(i=0;i<removed.size();i++){   
            clause_list.erase(clause_list.begin()+removed[i]-j);j++;
            
        }
        removed.clear();

        //Now we will  search for negation of the literal and remove its appearance from 
        // the clauses.
        
        for(i=0;i<clause_list.size();i++){
            if(binary_search(clause_list[i].begin(),clause_list[i].end(),-1*x)){
                auto it = find(clause_list[i].begin(),clause_list[i].end(),-1*x);
                if(it!=clause_list[i].end())clause_list[i].erase(it);

            }
        }

        return clause_list; // Returns the reshaped clause list   
    }

    /* This function is used to find all the pure literals i.e. the literals which are either always positive
or always negative in whole cnf  .

Also we add all these pure literals to the model and then reshape the clauses list.
*/


vector<vector<int>> pure_elimination( int literals, vector<vector<int>> clause_list){
        int clauses= clause_list.size();
        int i;
        for(i=1;i<=literals;i++){
            int pos=0,flag=0;
            for(int j=0;j<clauses;j++){
                
                if((pos==0 || pos==1) && binary_search(clause_list[j].begin(),clause_list[j].end(),i)){
                    pos=1;
                }//if a literal always occurs only in positive form

                else if((pos==0 || pos==-1) && binary_search(clause_list[j].begin(),clause_list[j].end(),-1*i)){
                    pos=-1;
                }//if a literal always occurs only in negative form

                else if(binary_search(clause_list[j].begin(),clause_list[j].end(),i) ||
                binary_search(clause_list[j].begin(),clause_list[j].end(),-1*i)){
                    flag=1;break;
                }// if a literal is in both neg and pos form then dont check fo it and continue to next literal
            }
            if(flag==0 && pos!=0){model.push_back(i*pos);reshape_clauses(i*pos,clause_list);}
            
        }    
        return clause_list;   
    }


 /*
 This function is to look for the literal from the given clause with appearance in maximum number of clauses which
 will be efficient as we can deal with maximum number of clauses at a time
 */      

int which_literal_to_use(vector<int> smallest_clause, vector<vector<int>> clause_list){
        
        int n = smallest_clause.size();
        vector<int> apperance(n,0);     // it will store the number of clauses in which a literal appears
        for(int i=0;i<n;i++){
            for(int j=0;j<clause_list.size();j++){
                if(binary_search(clause_list[j].begin(),clause_list[j].end(),smallest_clause[i])){
                    apperance[i]++;
                }   
            }    
        }
        int max_appearance=0;
        int index=-1;
        for(int i=0;i<n;i++){
            if(apperance[i]>max_appearance){
                max_appearance=apperance[i];
                index=i;
            }
        }

        return index;  // returns the index of literal from the given clause which has appearance in max number of clauses 
    }


/*
This function returns the clause with least number of literals which facilitates in 
faster checking of satisfiabilty
*/

int smallest_clause(vector<vector<int>> claus){
        
        int i,mini=10000000,index=-1;
        for(i=0;i<claus.size();i++){
            if(claus[i].size()<mini){mini=claus[i].size();index=i;}

        }     
        return index;
    }


/*
This function checks for unit length clauses and assign them values and reshape the clauses list
*/

    vector<vector<int>> unit_Propagation(int clauses, int literals, vector<vector<int>> clause_list){

            for(int j=0;j<clauses;j++){
                if(clause_list[j].size()==1){
                    
                    model.push_back(clause_list[j][0]);
                    clause_list=reshape_clauses(clause_list[j][0],clause_list);
                    
                }
            }
            return clause_list;
                    
    }

/*
This is the recursive function to implement the DPLL algorithm where we use backtracking method to assign values to propositions
and then cheking satisfiability.
*/
   

int solver(vector<vector<int>> claus){

        int clauses = claus.size();  
        if(clauses==0){return 1;}     // Base case => there is no clause, i.e always satisfiable

        int index = smallest_clause(claus);  
         if(claus[index].size()==0)return 0;  // If any clause has length 0, then we have unsatisfiability 

        int index1= which_literal_to_use(claus[index],claus);

        model.push_back(claus[index][index1]);
        if(solver(reshape_clauses(claus[index][index1],claus)))return 1;  // if we get a solution after keeping claus[index][index1
                                                                          // in the model, we return 1;
         
        else {
            model.pop_back();                                             // else we remove this literal and keep its negation in model 
           
            model.push_back(-1*claus[index][index1]);                     
            if(solver(reshape_clauses(-1*claus[index][index1],claus)))return 1; // again we check for satisfiability , if it is sat, we return 1
            else {model.pop_back();return 0;}                                   // else the formula is unsat. as we tried both the literal and its negation 
                                                                                // but both of them gives unsatisfiable 
        }

        return 0;
    }



int main(){

    int i,j,k;
    int clauses, literals;  

    vector<vector<int>> clause_list;
    
    clock_t start = clock();

    // start of Reading input

    freopen("test_cases/test2.cnf", "r", stdin);

    char y[1000000];
    while(1){
       scanf("%[^\n]%*c", y);
       if(y[0]=='c')continue;
       if(y[0]=='p'){
           
        istringstream stream(y);
        vector<string>y1((istream_iterator<string>(stream)),istream_iterator<string>());
        clauses=stoi(y1[3]);
        literals=stoi(y1[2]);
       }

       clause_list.resize(clauses);

       
       // Storing all the clauses in a vector\

       for(i =0;i< clauses;i++){
           scanf("%[^\n]%*c", y);
           if(y[0]=='c'){i--;continue;}
           else {
               istringstream stream(y);
               vector<string>y2((istream_iterator<string>(stream)),istream_iterator<string>());
               int n = y2.size();
               for(j=0;j<n;j++){
                   int prop = stoi(y2[j]);
                   
                   if(prop!=0){
                       clause_list[i].push_back(prop);   
                   }
               }    
           }     
       }
       
       break;
    }

    // End of reading input 


     for(i=0;i<clauses;i++){
         sort(clause_list[i].begin(),clause_list[i].end());
     }
     int init_clauses = clauses;
     vector<vector<int>> initial_clauses_list = clause_list;
     clause_list = unit_Propagation(clauses,literals,clause_list); // First we will start with unit Propagation 
     clauses=clause_list.size();
    
     clause_list = pure_elimination(literals,clause_list); // Then we will work around for all the pure_literals 

     clauses=clause_list.size();
     
     
     int z=solver(clause_list);
    
    if(z==0){cout<<"UNSAT";return 0;} // If we get no model we will display UNSAT message 

    
     vector<int> sol1,sol2;           // In sol1, we will keep negtve literals and in sol2, we will keep postive ones
     sort(model.begin(),model.end());

     for(i=1;i<=literals;i++){
         if(binary_search(model.begin(),model.end(),i));
         else if(binary_search(model.begin(),model.end(),-1*i));
         else {model.push_back(i);}                              // if any proposition is not assigned a value, then we will assign it TRUE
     } 

     sort(model.begin(),model.end());
     
     
     model.erase( unique( model.begin(), model.end() ), model.end() );
     for(i=0;i<model.size();i++){
         if(model[i]<0)sol1.push_back(model[i]);
         else sol2.push_back(model[i]);
     }

    vector<int> final_model;
     i=0;j=sol1.size()-1;k=0;
     for(i=0;i<model.size();i++){
         if(j<0){final_model.push_back(sol2[k]);k++;}
         else if(k>sol2.size()-1){final_model.push_back(sol1[j]);j--;}
         else if(-1*sol1[j]>sol2[k]){final_model.push_back(sol2[k]);k++;}
         else {final_model.push_back(sol1[j]);j--;}

     }

     cout<<"SAT"<<endl;


     for(i=0;i<literals;i++)cout<<final_model[i]<<" ";      // To print the final model

     // The commented code below is to verify if all the clauses are satisfied or not

     
//      sort(final_model.begin(),final_model.end());
// int d=0;

//      for(i=0;i<init_clauses;i++){
//          for(j=0;j<initial_clauses_list[i].size();j++){
            
//              if(binary_search(final_model.begin(),final_model.end(),initial_clauses_list[i][j])){
//                  d++;
                
//                  break;

//              }
//          }
//      }
//     cout<<endl<<d;
     
    return 0;

}
   