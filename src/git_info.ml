(*
  git hash and date of the last commit 
  auto generated by git_info script
  do not modify by hand
  do not add to git
*)

type git_info = 
    {
     git_sha1 : string;
     git_date : string;
     git_non_committed_changes : bool;
   }


let git_info = 
    {
     git_sha1 = "263da1dcf6ef464b42620270e62a9f384f34fa7e";
     git_date = "2021-05-07 14:34:04 +0200"; 
     git_non_committed_changes =true;
   }

let make_outside_git = ref false;;
