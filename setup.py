import setuptools

with open("README.md", "r") as fh:
    long_description = fh.read()

with open('requirements.txt', 'r') as fh:
    requirements = fh.read().split('\n')

setuptools.setup(
    name="PWE_Diagnostic_Lattice_Tool",
    version="0.0.2",
    author="Sahil Gupta",
    author_email="",
    description="Companion Tool to PWE for problems with switchable constraints.",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/idaks/PWE-Diagnostic-Lattice-Tool",
    packages=setuptools.find_packages(),
    install_requires=requirements,
    classifiers=[
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: Apache Software License",
        "Operating System :: OS Independent",
    ],
)
