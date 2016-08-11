open relational_properties_tagged as relational_properties
pred SzGrwtStrcNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | (c in c' )  and (c' !in c )
}
pred SzShrnk_Glbl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) |(c' in c )
}
pred SzShrnk_Lcl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' |(c' in c )
}
pred SzShrnkNOP_Glbl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right |(c' in c )
}
pred SzShrnkNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' |(c' in c )
}
pred SzShrnkNOP_Lcl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' |(c' in c )
}
pred SzShrnk_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) |(c' in c )
}
pred SzShrnk_Lcl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) |(c' in c )
}
pred SzShrnk_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) |(c' in c )
}
pred SzShrnk_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' |(c' in c )
}
pred SzShrnk_Glbl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right |(c' in c )
}
pred SzShrnk_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right |(c' in c )
}
pred SzNChngNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | eq[#c' ,# c]
}
pred SzNChngNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | eq[#c' ,# c]
}
pred SzNChngNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | eq[#c' ,# c]
}
pred SzShrnkNOP_Glbl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) |(c' in c )
}
pred SzShrnkStrc_Glbl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) |(c' in c ) and (c !in c' )
}
pred SzShrnkNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) |(c' in c )
}
pred SzShrnkStrc_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) |(c' in c ) and (c !in c' )
}
pred SzShrnkStrc_Lcl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' |(c' in c ) and (c !in c' )
}
pred SzShrnkNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) |(c' in c )
}
pred SzShrnkStrc_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right |(c' in c ) and (c !in c' )
}
pred SzShrnkNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right |(c' in c )
}
pred SzShrnkStrc_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) |(c' in c ) and (c !in c' )
}
pred SzShrnkNOP_Lcl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) |(c' in c )
}
pred SzShrnkStrcNOP_Glbl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) |(c' in c ) and (c !in c' )
}
pred SzShrnkStrcNOP_Lcl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) |(c' in c ) and (c !in c' )
}
pred SzShrnkStrcNOP_Glbl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right |(c' in c ) and (c !in c' )
}
pred SzShrnkStrcNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) |(c' in c ) and (c !in c' )
}
pred SzShrnkStrc_Lcl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) |(c' in c ) and (c !in c' )
}
pred SzShrnkStrc_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' |(c' in c ) and (c !in c' )
}
pred SzShrnkStrcNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) |(c' in c ) and (c !in c' )
}
pred SzShrnkStrcNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' |(c' in c ) and (c !in c' )
}
pred SzShrnkStrcNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right |(c' in c ) and (c !in c' )
}
pred SzShrnkStrcNOP_Lcl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' |(c' in c ) and (c !in c' )
}
pred SzShrnkStrc_Glbl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right |(c' in c ) and (c !in c' )
}
pred SzGrwt_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | (c in c' ) 
}
pred SzGrwt_Lcl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | (c in c' ) 
}
pred SzGrwt_Glbl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | (c in c' ) 
}
pred SzGrwt_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | (c in c' ) 
}
pred SzGrwt_Glbl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | (c in c' ) 
}
pred SzGrwt_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | (c in c' ) 
}
pred SzGrwt_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | (c in c' ) 
}
pred SzGrwt_Lcl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | (c in c' ) 
}
pred SzGrwtNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | (c in c' ) 
}
pred SzGrwtNOP_Lcl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | (c in c' ) 
}
pred SzGrwtNOP_Glbl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | (c in c' ) 
}
pred SzGrwtNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | (c in c' ) 
}
pred SzGrwtNOP_Lcl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | (c in c' ) 
}
pred SzGrwtNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | (c in c' ) 
}
pred SzGrwtStrc_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | (c in c' )  and (c' !in c )
}
pred SzGrwtStrcNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | (c in c' )  and (c' !in c )
}
pred SzGrwtStrc_Lcl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | (c in c' )  and (c' !in c )
}
pred SzGrwtStrc_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | (c in c' )  and (c' !in c )
}
pred SzGrwtStrc_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | (c in c' )  and (c' !in c )
}
pred SzGrwtStrcNOP_Lcl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | (c in c' )  and (c' !in c )
}
pred SzGrwtStrc_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | (c in c' )  and (c' !in c )
}
pred SzGrwtNOP_Glbl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | (c in c' ) 
}
pred SzGrwtStrc_Glbl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | (c in c' )  and (c' !in c )
}
pred SzGrwtStrc_Lcl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | (c in c' )  and (c' !in c )
}
pred SzGrwtNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | (c in c' ) 
}
pred SzGrwtStrc_Glbl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | (c in c' )  and (c' !in c )
}
pred SzNChng_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | eq[#c' ,# c]
}
pred SzNChng_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | eq[#c' ,# c]
}
pred SzNChng_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | eq[#c' ,# c]
}
pred SzGrwtStrcNOP_Glbl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | (c in c' )  and (c' !in c )
}
pred SzGrwtStrcNOP_Glbl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | (c in c' )  and (c' !in c )
}
pred SzGrwtStrcNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | (c in c' )  and (c' !in c )
}
pred SzGrwtStrcNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | (c in c' )  and (c' !in c )
}
pred SzGrwtStrcNOP_Lcl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | (c in c' )  and (c' !in c )
}
pred SzNChng_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | eq[#c' ,# c]
}
pred SzNChngNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | eq[#c' ,# c]
}
pred OrdIncrs_SzShrnk_Glbl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (c' in c ) and   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdDcrs_SzShrnk_Glbl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (c' in c ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c',right_next],right_next] ) )
}
pred OrdDcrs_SzGrwt_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |   (c in c' ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c,right_next],right_next] ) )
}
pred OrdDcrs_SzGrwtStrcNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c,right_next],right_next] ) )
}
pred OrdDcrs_SzGrwtStrc_Glbl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c,middle_next],middle_next] ) )
}
pred OrdDcrs_SzShrnk_Lcl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (c' in c ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c',middle_next],middle_next] ) )
}
pred OrdDcrs_SzShrnk_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (c' in c ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c',right_next],right_next] ) )
}
pred OrdDcrs_SzGrwtStrcNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c,middle_next],middle_next] ) )
}
pred OrdDcrs_SzShrnk_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (c' in c ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c',right_next],right_next] ) )
}
pred OrdDcrs_SzShrnkNOP_Lcl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c',right_next],right_next] ) )
}
pred OrdDcrs_SzGrwtStrcNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c,right_next],right_next] ) )
}
pred OrdDcrs_SzNChngNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |    (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c,right_next],right_next] ) )
}
pred OrdDcrs_SzNChngNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |    (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c,middle_next],middle_next] ) )
}
pred OrdDcrs_SzNChng_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |  eq[#c' ,# c] and  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c,right_next],right_next] ) )
}
pred OrdDcrs_SzShrnk_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (c' in c ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c',middle_next],middle_next] ) )
}
pred OrdDcrs_SzShrnkNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c',right_next],right_next] ) )
}
pred OrdDcrs_SzNChng_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |  eq[#c' ,# c] and  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c,middle_next],middle_next] ) )
}
pred OrdDcrs_SzGrwtNOP_Lcl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c,middle_next],middle_next] ) )
}
pred OrdDcrs_SzShrnkStrc_Lcl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c',right_next],right_next] ) )
}
pred OrdDcrs_SzGrwtNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c,middle_next],middle_next] ) )
}
pred OrdDcrs_SzShrnkStrc_Lcl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c',middle_next],middle_next] ) )
}
pred OrdDcrs_SzGrwtStrcNOP_Lcl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c,middle_next],middle_next] ) )
}
pred OrdDcrs_SzGrwtStrc_Glbl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c,right_next],right_next] ) )
}
pred OrdDcrs_SzShrnkStrc_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c',right_next],right_next] ) )
}
pred OrdDcrs_SzGrwtNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c,right_next],right_next] ) )
}
pred OrdDcrs_SzShrnk_Glbl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (c' in c ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c',middle_next],middle_next] ) )
}
pred OrdDcrs_SzNChng_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |  eq[#c' ,# c] and  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c,middle_next],middle_next] ) )
}
pred OrdDcrs_SzShrnkStrcNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c',middle_next],middle_next] ) )
}
pred OrdDcrs_SzShrnkNOP_Lcl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c',middle_next],middle_next] ) )
}
pred OrdDcrs_SzGrwt_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |   (c in c' ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c,middle_next],middle_next] ) )
}
pred OrdDcrs_SzGrwtNOP_Lcl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c,right_next],right_next] ) )
}
pred OrdDcrs_SzShrnkStrcNOP_Lcl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c',middle_next],middle_next] ) )
}
pred OrdDcrs_SzShrnkStrcNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c',right_next],right_next] ) )
}
pred OrdDcrs_SzShrnkStrc_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c',right_next],right_next] ) )
}
pred OrdDcrs_SzShrnkStrcNOP_Glbl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c',right_next],right_next] ) )
}
pred OrdDcrs_SzShrnk_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (c' in c ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c',middle_next],middle_next] ) )
}
pred OrdDcrs_SzGrwtStrcNOP_Glbl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c,middle_next],middle_next] ) )
}
pred OrdDcrs_SzShrnkStrcNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c',right_next],right_next] ) )
}
pred OrdDcrs_SzGrwtStrcNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c,middle_next],middle_next] ) )
}
pred OrdDcrs_SzGrwtNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c,middle_next],middle_next] ) )
}
pred OrdDcrs_SzGrwt_Glbl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |   (c in c' ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c,right_next],right_next] ) )
}
pred OrdDcrs_SzShrnk_Lcl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (c' in c ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c',right_next],right_next] ) )
}
pred OrdDcrs_SzShrnkNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c',middle_next],middle_next] ) )
}
pred OrdDcrs_SzShrnkStrc_Glbl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c',middle_next],middle_next] ) )
}
pred OrdDcrs_SzGrwtStrcNOP_Glbl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c,right_next],right_next] ) )
}
pred OrdDcrsStrc_SzShrnk_Glbl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (c' in c ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c',right_next],right_next] ) )
}
pred OrdIncrsStrc_SzShrnk_Glbl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (c' in c ) and   (some delta implies relational_properties/lt[relational_properties/max[c',right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzNChngNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |    (some delta implies relational_properties/lt[relational_properties/max[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzNChngNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |    (some delta implies relational_properties/lt[relational_properties/max[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzShrnkStrcNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (some delta implies relational_properties/lt[relational_properties/max[c',right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzShrnkNOP_Lcl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (some delta implies relational_properties/lt[relational_properties/max[c',middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzGrwtNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |   (some delta implies relational_properties/lt[relational_properties/max[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzGrwtStrc_Lcl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies relational_properties/lt[relational_properties/max[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzShrnkStrc_Lcl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies relational_properties/lt[relational_properties/max[c',right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzGrwt_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |   (c in c' ) and   (some delta implies relational_properties/lt[relational_properties/max[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzGrwt_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |   (c in c' ) and   (some delta implies relational_properties/lt[relational_properties/max[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzShrnkStrc_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies relational_properties/lt[relational_properties/max[c',right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzGrwtNOP_Lcl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |   (some delta implies relational_properties/lt[relational_properties/max[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzGrwtStrcNOP_Lcl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |  (some delta implies relational_properties/lt[relational_properties/max[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzShrnkStrc_Lcl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies relational_properties/lt[relational_properties/max[c',middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzShrnkStrcNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (some delta implies relational_properties/lt[relational_properties/max[c',right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzGrwtNOP_Glbl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |   (some delta implies relational_properties/lt[relational_properties/max[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdDcrs_SzShrnkNOP_Glbl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c',right_next],right_next] ) )
}
pred OrdDcrs_SzNChngNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |    (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c,right_next],right_next] ) )
}
pred OrdDcrs_SzGrwtStrc_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c,middle_next],middle_next] ) )
}
pred OrdDcrs_SzGrwt_Lcl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |   (c in c' ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c,middle_next],middle_next] ) )
}
pred OrdDcrs_SzGrwtStrc_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c,middle_next],middle_next] ) )
}
pred OrdDcrs_SzShrnkStrc_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c',middle_next],middle_next] ) )
}
pred OrdDcrs_SzGrwt_Glbl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |   (c in c' ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c,middle_next],middle_next] ) )
}
pred OrdDcrs_SzNChng_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |  eq[#c' ,# c] and  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c,right_next],right_next] ) )
}
pred OrdDcrs_SzGrwtNOP_Glbl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c,right_next],right_next] ) )
}
pred OrdDcrs_SzGrwtStrcNOP_Lcl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c,right_next],right_next] ) )
}
pred OrdDcrs_SzShrnkStrc_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c',middle_next],middle_next] ) )
}
pred OrdDcrs_SzShrnkStrcNOP_Glbl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c',middle_next],middle_next] ) )
}
pred OrdDcrs_SzGrwt_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |   (c in c' ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c,middle_next],middle_next] ) )
}
pred OrdDcrs_SzNChngNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |    (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c,middle_next],middle_next] ) )
}
pred OrdDcrs_SzShrnkStrcNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c',middle_next],middle_next] ) )
}
pred OrdDcrs_SzGrwt_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |   (c in c' ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c,right_next],right_next] ) )
}
pred OrdDcrs_SzShrnkNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c',middle_next],middle_next] ) )
}
pred OrdDcrs_SzShrnkNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c',right_next],right_next] ) )
}
pred OrdDcrs_SzGrwtStrc_Lcl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c,right_next],right_next] ) )
}
pred OrdDcrs_SzShrnkStrcNOP_Lcl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c',right_next],right_next] ) )
}
pred OrdDcrs_SzGrwtNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c,right_next],right_next] ) )
}
pred OrdDcrs_SzGrwt_Lcl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |   (c in c' ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c,right_next],right_next] ) )
}
pred OrdDcrs_SzShrnkNOP_Glbl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c',middle_next],middle_next] ) )
}
pred OrdDcrs_SzGrwtStrc_Lcl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c,middle_next],middle_next] ) )
}
pred OrdDcrs_SzGrwtStrc_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c,right_next],right_next] ) )
}
pred OrdDcrs_SzGrwtNOP_Glbl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/max[c,middle_next],middle_next] ) )
}
pred OrdDcrs_SzGrwtStrc_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c,right_next],right_next] ) )
}
pred OrdDcrsStrc_SzGrwtStrcNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c,right_next],right_next] ) )
}
pred OrdDcrsStrc_SzNChngNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |    (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c,right_next],right_next] ) )
}
pred OrdDcrsStrc_SzGrwtStrcNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c,middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzGrwtStrcNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c,middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzNChng_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |  eq[#c' ,# c] and  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c,right_next],right_next] ) )
}
pred OrdDcrsStrc_SzGrwtStrc_Glbl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c,right_next],right_next] ) )
}
pred OrdDcrsStrc_SzShrnkNOP_Glbl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c',right_next],right_next] ) )
}
pred OrdDcrsStrc_SzShrnkStrcNOP_Glbl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c',right_next],right_next] ) )
}
pred OrdDcrsStrc_SzGrwtStrc_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c,right_next],right_next] ) )
}
pred OrdDcrsStrc_SzGrwtNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c,middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzGrwtStrc_Glbl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c,middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzGrwtNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c,right_next],right_next] ) )
}
pred OrdDcrsStrc_SzGrwtStrcNOP_Glbl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c,middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzShrnkNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c',middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzShrnkStrc_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c',right_next],right_next] ) )
}
pred OrdDcrsStrc_SzShrnk_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (c' in c ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c',middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzShrnkNOP_Lcl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c',middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzNChngNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |    (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c,middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzShrnk_Lcl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (c' in c ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c',middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzGrwt_Lcl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |   (c in c' ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c,right_next],right_next] ) )
}
pred OrdDcrsStrc_SzGrwt_Lcl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |   (c in c' ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c,middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzGrwtStrc_Lcl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c,middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzGrwtNOP_Lcl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c,right_next],right_next] ) )
}
pred OrdDcrsStrc_SzShrnkStrc_Lcl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c',right_next],right_next] ) )
}
pred OrdDcrsStrc_SzShrnkStrcNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c',right_next],right_next] ) )
}
pred OrdDcrsStrc_SzShrnkStrc_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c',middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzGrwtNOP_Lcl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c,middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzShrnkStrcNOP_Glbl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c',middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzGrwtStrc_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c,middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzGrwtStrcNOP_Lcl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c,middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzGrwt_Glbl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |   (c in c' ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c,right_next],right_next] ) )
}
pred OrdIncrs_SzShrnkNOP_Glbl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzShrnkStrc_Glbl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies relational_properties/lt[relational_properties/max[c',right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzNChng_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |  eq[#c' ,# c] and  (some delta implies relational_properties/lt[relational_properties/max[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzShrnkStrcNOP_Glbl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (some delta implies relational_properties/lt[relational_properties/max[c',middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzShrnkNOP_Lcl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (some delta implies relational_properties/lt[relational_properties/max[c',right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzNChng_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |  eq[#c' ,# c] and  (some delta implies relational_properties/lt[relational_properties/max[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzGrwt_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |   (c in c' ) and   (some delta implies relational_properties/lt[relational_properties/max[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzShrnkStrc_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies relational_properties/lt[relational_properties/max[c',middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzShrnkStrc_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies relational_properties/lt[relational_properties/max[c',right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzGrwtStrcNOP_Glbl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |  (some delta implies relational_properties/lt[relational_properties/max[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzGrwtStrc_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies relational_properties/lt[relational_properties/max[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzShrnk_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (c' in c ) and   (some delta implies relational_properties/lt[relational_properties/max[c',middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzGrwtStrc_Glbl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies relational_properties/lt[relational_properties/max[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzShrnk_Lcl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (c' in c ) and   (some delta implies relational_properties/lt[relational_properties/max[c',middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzShrnkNOP_Glbl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (some delta implies relational_properties/lt[relational_properties/max[c',middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzGrwtNOP_Glbl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |   (some delta implies relational_properties/lt[relational_properties/max[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzGrwtNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |   (some delta implies relational_properties/lt[relational_properties/max[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzNChng_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |  eq[#c' ,# c] and  (some delta implies relational_properties/lt[relational_properties/max[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzGrwtStrcNOP_Lcl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |  (some delta implies relational_properties/lt[relational_properties/max[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzShrnk_Glbl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (c' in c ) and   (some delta implies relational_properties/lt[relational_properties/max[c',middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzGrwtStrcNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |  (some delta implies relational_properties/lt[relational_properties/max[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzShrnkStrcNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (some delta implies relational_properties/lt[relational_properties/max[c',middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzGrwtStrc_Glbl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies relational_properties/lt[relational_properties/max[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzGrwtNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |   (some delta implies relational_properties/lt[relational_properties/max[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzGrwtStrc_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies relational_properties/lt[relational_properties/max[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzShrnk_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (c' in c ) and   (some delta implies relational_properties/lt[relational_properties/max[c',right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzShrnkStrcNOP_Lcl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (some delta implies relational_properties/lt[relational_properties/max[c',right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzShrnkStrc_Glbl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies relational_properties/lt[relational_properties/max[c',middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzNChng_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |  eq[#c' ,# c] and  (some delta implies relational_properties/lt[relational_properties/max[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzShrnkNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (some delta implies relational_properties/lt[relational_properties/max[c',middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzGrwt_Lcl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |   (c in c' ) and   (some delta implies relational_properties/lt[relational_properties/max[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzShrnkNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (some delta implies relational_properties/lt[relational_properties/max[c',middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzGrwt_Lcl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |   (c in c' ) and   (some delta implies relational_properties/lt[relational_properties/max[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzNChngNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |    (some delta implies relational_properties/lt[relational_properties/max[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzGrwtNOP_Lcl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |   (some delta implies relational_properties/lt[relational_properties/max[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzNChngNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |    (some delta implies relational_properties/lt[relational_properties/max[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzShrnkNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (some delta implies relational_properties/lt[relational_properties/max[c',right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzGrwtStrc_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies relational_properties/lt[relational_properties/max[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzGrwtStrc_Lcl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies relational_properties/lt[relational_properties/max[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzShrnk_Lcl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (c' in c ) and   (some delta implies relational_properties/lt[relational_properties/max[c',right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzGrwtStrcNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |  (some delta implies relational_properties/lt[relational_properties/max[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzGrwtStrcNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |  (some delta implies relational_properties/lt[relational_properties/max[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzGrwt_Glbl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |   (c in c' ) and   (some delta implies relational_properties/lt[relational_properties/max[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzShrnkStrcNOP_Lcl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (some delta implies relational_properties/lt[relational_properties/max[c',middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzShrnkStrc_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies relational_properties/lt[relational_properties/max[c',middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzShrnk_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (c' in c ) and   (some delta implies relational_properties/lt[relational_properties/max[c',right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzShrnkStrcNOP_Glbl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (some delta implies relational_properties/lt[relational_properties/max[c',right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzGrwt_Glbl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |   (c in c' ) and   (some delta implies relational_properties/lt[relational_properties/max[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzShrnk_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (c' in c ) and   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzGrwtNOP_Lcl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzShrnkNOP_Lcl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzGrwtStrcNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |  (some delta implies relational_properties/lt[relational_properties/max[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzShrnkStrcNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (some delta implies relational_properties/lt[relational_properties/max[c',middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzShrnkStrc_Lcl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzShrnkNOP_Glbl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzGrwtStrcNOP_Glbl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |  (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzShrnkStrcNOP_Lcl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzShrnkNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (some delta implies relational_properties/lt[relational_properties/max[c',right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzGrwtStrcNOP_Glbl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |  (some delta implies relational_properties/lt[relational_properties/max[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzGrwtStrc_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies relational_properties/lt[relational_properties/max[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzGrwtNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |   (some delta implies relational_properties/lt[relational_properties/max[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrsStrc_SzShrnk_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (c' in c ) and   (some delta implies relational_properties/lt[relational_properties/max[c',middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzGrwtNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzGrwt_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |   (c in c' ) and   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzNChng_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |  eq[#c' ,# c] and  (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzGrwtNOP_Glbl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzShrnkStrc_Lcl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzShrnkNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzShrnk_Lcl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (c' in c ) and   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzShrnkStrc_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzShrnk_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (c' in c ) and   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzGrwtNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzGrwtStrc_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzGrwtStrc_Glbl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzNChng_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |  eq[#c' ,# c] and  (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzGrwt_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |   (c in c' ) and   (some delta implies relational_properties/lt[relational_properties/max[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrsStrc_SzShrnkNOP_Glbl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (some delta implies relational_properties/lt[relational_properties/max[c',right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdDcrs_SzShrnkStrc_Glbl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/max[c',right_next],right_next] ) )
}
pred OrdDcrsStrc_SzShrnkStrc_Glbl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c',right_next],right_next] ) )
}
pred OrdDcrsStrc_SzGrwtStrc_Lcl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c,right_next],right_next] ) )
}
pred OrdDcrsStrc_SzShrnk_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (c' in c ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c',middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzShrnkStrc_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c',middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzShrnkStrcNOP_Lcl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c',middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzNChng_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |  eq[#c' ,# c] and  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c,middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzGrwtNOP_Glbl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c,middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzGrwtStrcNOP_Lcl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c,right_next],right_next] ) )
}
pred OrdDcrsStrc_SzNChng_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |  eq[#c' ,# c] and  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c,right_next],right_next] ) )
}
pred OrdDcrsStrc_SzGrwtStrc_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c,right_next],right_next] ) )
}
pred OrdDcrsStrc_SzShrnkStrcNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c',middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzGrwtStrc_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c,middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzShrnkStrcNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c',right_next],right_next] ) )
}
pred OrdDcrsStrc_SzNChng_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |  eq[#c' ,# c] and  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c,middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzNChngNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |    (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c,middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzShrnkStrcNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c',middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzGrwt_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |   (c in c' ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c,middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzNChngNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |    (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c,right_next],right_next] ) )
}
pred OrdDcrsStrc_SzShrnk_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (c' in c ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c',right_next],right_next] ) )
}
pred OrdDcrsStrc_SzGrwtStrcNOP_Glbl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c,right_next],right_next] ) )
}
pred OrdDcrsStrc_SzShrnkNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c',right_next],right_next] ) )
}
pred OrdDcrsStrc_SzGrwt_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |   (c in c' ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c,middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzGrwtNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c,middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzShrnkStrc_Glbl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c',middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzShrnk_Lcl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (c' in c ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c',right_next],right_next] ) )
}
pred OrdDcrsStrc_SzGrwtNOP_Glbl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c,right_next],right_next] ) )
}
pred OrdDcrsStrc_SzShrnkNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c',right_next],right_next] ) )
}
pred OrdIncrs_SzShrnkStrcNOP_Glbl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzNChng_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |  eq[#c' ,# c] and  (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzShrnk_Lcl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (c' in c ) and   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzShrnk_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (c' in c ) and   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzShrnk_Glbl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (c' in c ) and   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzNChngNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |    (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzShrnkStrcNOP_Lcl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzGrwt_Lcl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |   (c in c' ) and   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzGrwt_Lcl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |   (c in c' ) and   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzGrwtStrc_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzGrwtStrc_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzGrwtNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzGrwt_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |   (c in c' ) and   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzGrwtStrcNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |  (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzGrwt_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |   (c in c' ) and   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzGrwtStrc_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdDcrsStrc_SzShrnk_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (c' in c ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c',right_next],right_next] ) )
}
pred OrdDcrsStrc_SzShrnkNOP_Lcl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c',right_next],right_next] ) )
}
pred OrdDcrsStrc_SzGrwtNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c,right_next],right_next] ) )
}
pred OrdDcrsStrc_SzShrnkStrc_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c',right_next],right_next] ) )
}
pred OrdDcrsStrc_SzGrwtStrcNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |  (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c,right_next],right_next] ) )
}
pred OrdDcrsStrc_SzGrwt_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |   (c in c' ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c,right_next],right_next] ) )
}
pred OrdDcrsStrc_SzShrnkNOP_Glbl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c',middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzShrnkStrc_Lcl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c',middle_next],middle_next] ) )
}
pred OrdDcrsStrc_SzShrnkNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c',middle_next],middle_next] ) )
}
pred OrdIncrs_SzGrwtStrcNOP_Glbl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |  (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzShrnkNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzShrnkStrcNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzGrwt_Glbl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |   (c in c' ) and   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzGrwtNOP_Glbl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdDcrsStrc_SzGrwt_Glbl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |   (c in c' ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c,middle_next],middle_next] ) )
}
pred OrdIncrs_SzShrnkStrc_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdDcrsStrc_SzShrnkStrcNOP_Lcl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c',right_next],right_next] ) )
}
pred OrdDcrsStrc_SzShrnk_Glbl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (c' in c ) and   (some delta implies(some c' implies relational_properties/lt[relational_properties/max[delta,middle_next],relational_properties/min[c',middle_next],middle_next] ) )
}
pred OrdIncrs_SzGrwtStrcNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |  (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzShrnkStrcNOP_Glbl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzGrwtStrcNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |  (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzShrnkStrcNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdDcrsStrc_SzGrwt_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |   (c in c' ) and   (some delta implies(some c implies relational_properties/lt[relational_properties/max[delta,right_next],relational_properties/min[c,right_next],right_next] ) )
}
pred OrdIncrs_SzShrnkStrc_Glbl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzGrwt_Glbl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |   (c in c' ) and   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzGrwt_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |   (c in c' ) and   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzGrwtStrcNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |  (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzShrnkNOP_Lcl_SdEnd_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzGrwtNOP_Lcl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzGrwtStrcNOP_Lcl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |  (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzGrwtStrcNOP_Lcl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |  (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzGrwtNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzNChng_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |  eq[#c' ,# c] and  (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzNChngNOP_Glbl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |    (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzGrwtStrc_Lcl_SdEnd_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzShrnkStrc_Glbl_SdMdl_EmptEnd_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no relational_properties/last[left,left_next].r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzShrnkStrc_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzShrnkStrcNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzShrnk_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c - c' |   (c' in c ) and   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzShrnkStrc_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (c' in c ) and   (c !in c' ) and   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzNChngNOP_Lcl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all middle' : middle| let c = middle'.(left'.r) |let c' = middle'.(left''.r) | let delta = c' - c |    (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzGrwtStrc_Lcl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzNChngNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c' - c |    (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzShrnkNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzShrnkNOP_Lcl_SdMdl_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
 all right' : right| let c = (left'.r).right' |let c' = (left''.r).right' | let delta = c - c' |   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}
pred OrdIncrs_SzShrnkStrcNOP_Glbl_SdEnd_EmptNon_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, right_first: univ, right_next: univ->univ]{

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = middle.(left'.r) |let c' = middle.(left''.r) | let delta = c - c' |   (some delta implies relational_properties/lte[relational_properties/min[c,right_next],relational_properties/min[delta,right_next],right_next] )
}
pred OrdIncrs_SzGrwtStrc_Glbl_SdMdl_EmptStrt_[r: univ->univ->univ, left, middle, right: univ, left_first: univ, left_next: univ->univ, middle_first: univ, middle_next: univ->univ]{
no left_first.r 

all left': left - relational_properties/last[left,left_next] |let left'' = left'.left_next |
let c = (left'.r).right |let c' = (left''.r).right | let delta = c' - c |  (c in c' ) and   (c' !in c ) and   (some delta implies relational_properties/lte[relational_properties/min[c,middle_next],relational_properties/min[delta,middle_next],middle_next] )
}

