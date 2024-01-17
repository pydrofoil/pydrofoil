import os
from hypothesis import settings

settings.register_profile("ci", max_examples=2000, deadline=5000)
settings.register_profile("coverage", deadline=None)

settings.load_profile(os.getenv("HYPOTHESIS_PROFILE", "default"))

