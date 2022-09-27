
# Make the tactics have a separate auxiliary function to return the actual proof term
# so we don't have to use evalTactic and keep refreshing the context

# Create a core for each tactic so that we don't have to use it with Syntax,
# but with sets of Expr/Name (easier to manipulate)

