from racks_model import RackConfiguration


def test_model():

    configuration = RackConfiguration()
    assert configuration.get_violated_constraints() == []

    configuration.create_object(1,1,RackConfiguration.RACKSINGLE)
    assert len(configuration.get_violated_constraints()) > 0




