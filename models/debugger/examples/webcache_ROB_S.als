module webcache
sig Time {}
sig URL {}
//A Server records (at most) one Page
// per URL at any given time.
sig Server {page: Time -> URL ->lone Page}
//Page expiration is modeled by a set
// of times at which the page is fresh.
sig Page {life: set Time}                     
//Page recorded by any Server is fresh
fact ServerFresh {
	all s:Server, t:Time, u:URL, p:Page |
		(t -> u -> p) in s.page => t in p.life 
}
//The cache may drop & add entries
// from the owner, but no stale pages
// may remain afterwards
pred Get [t,t':Time, cache,owner:Server,u:URL, p:Page] {
	cache.page[t'] in cache.page[t]+ owner.page[t] - {u:URL, p:Page | t' not in p.life}
			=> p in (cache+owner).page[t'][u] }
//result of Get is always a fresh page
assert Freshness {
	all t,t':Time, cache,owner:Server, u:URL, p:Page |
		Get [t, t', cache, owner, u, p]=> t' in p.life 
}
check Freshness
